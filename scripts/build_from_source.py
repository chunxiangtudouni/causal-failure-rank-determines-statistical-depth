#!/usr/bin/env python3
"""Prepare an isolated Lake workspace, optionally building its Lean sources.

The accepted sources and Lake files are never edited.  Preparation needs
Python 3.11+, but neither Lean nor network access.  --build is explicit.
The generated library uses exact module globs supported by Lake v4.35.0.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

if sys.version_info < (3, 11):
    raise SystemExit("Python 3.11 or later is required for this source-build helper.")
import tomllib


SCHEMA = "causal-failure-rank.source-build.v1"
PACKAGE = "causal_failure_rank_source_build"
LIBRARY = "ProofSources"
TOOLCHAIN = "leanprover/lean4:v4.35.0"
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
EXTERNAL_ROOTS = {
    "Init", "Lean", "Std", "Lake", "Mathlib", "Aesop", "Batteries",
    "Qq", "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient", "Cli",
}
# Schema and CLI references, pinned to the version used by this project.
SCHEMA_SOURCES = [
    "https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/Config/LeanLibConfig.lean",
    "https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/Load/Toml.lean",
    "https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/CLI/Main.lean",
]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def uncomment(text: str) -> str:
    """Remove nested Lean comments and string contents, retaining line breaks."""
    result = []
    i, depth, quoted = 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        char = text[i]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            if char == "\\":
                result.extend("  ")
                i += 2
            else:
                quoted = char != '"'
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                result.extend(" " * (len(text) - i))
                break
            result.extend(" " * (end - i))
            i = end
        elif char == '"':
            quoted = True
            result.append(" ")
            i += 1
        else:
            result.append(char)
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment.")
    return "".join(result)


def imports(text: str) -> set[str]:
    found = set()
    for line in uncomment(text).splitlines():
        match = re.match(
            r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+?)\s*$",
            line,
        )
        if match:
            for name in match[1].split():
                if not MODULE.fullmatch(name):
                    raise ValueError(f"Unsupported import header token: {name!r}")
                found.add(name)
    return found


def collect_sources(repo: Path) -> tuple[dict, dict]:
    project = repo / "formalization/lean"
    private = project / "ProofDeps/MainD_Original_014"
    manifest = json.loads((private / "proof-manifest.json").read_text())
    sources: dict[str, dict] = {}

    def add(name: str, source: Path, owner: str) -> None:
        if not MODULE.fullmatch(name):
            raise ValueError(f"Unsupported module name: {name!r}")
        if name in sources:
            raise ValueError(f"Duplicate module {name}: {source} and {sources[name]['source']}")
        if not source.is_file():
            raise ValueError(f"Missing source for module {name}: {source}")
        raw = source.read_bytes()
        sources[name] = {
            "source": source.relative_to(repo).as_posix(),
            "destination": "src/" + name.replace(".", "/") + ".lean",
            "owner": owner,
            "bytes": len(raw),
            "sha256": digest(raw),
            "imports": sorted(imports(raw.decode("utf-8-sig"))),
        }

    for path in sorted(list((project / "PaperProofs").rglob("*.lean")) + list(project.glob("*.lean"))):
        name = path.relative_to(project).with_suffix("").as_posix().replace("/", ".")
        add(name, path, "formal")
    for entry in manifest["sources"]:
        source = private / entry["source"]["path"]
        if not source.resolve().is_relative_to(private.resolve()):
            raise ValueError(f"Private source escapes its package: {source}")
        add(entry["module"], source, "proof-dependency")
        actual = set(sources[entry["module"]]["imports"])
        expected = set(entry.get("imports", []))
        if actual != expected:
            raise ValueError(f"Import header differs from frozen inventory for {entry['module']}: "
                             f"added={sorted(actual - expected)}, missing={sorted(expected - actual)}")
    expected_count = manifest["counts"]["private_sources"]
    if sum(v["owner"] == "proof-dependency" for v in sources.values()) != expected_count:
        raise ValueError("The private source count differs from its manifest.")
    return sources, manifest


def check_graph(sources: dict) -> dict:
    local = set(sources)
    dependencies = {}
    unknown = []
    external = set()
    crossing = 0
    for name, entry in sources.items():
        dependencies[name] = set()
        for dep in entry["imports"]:
            if dep in local:
                dependencies[name].add(dep)
                if (entry["owner"] == "proof-dependency"
                        and sources[dep]["owner"] == "formal"):
                    crossing += 1
            elif dep.split(".")[0] in EXTERNAL_ROOTS:
                external.add(dep)
            else:
                unknown.append((name, dep))
    if unknown:
        raise ValueError(f"Unresolved internal imports: {unknown[:12]}")
    pending = {name: len(deps) for name, deps in dependencies.items()}
    dependents = defaultdict(set)
    for name, deps in dependencies.items():
        for dep in deps:
            dependents[dep].add(name)
    ready = deque(sorted(name for name, count in pending.items() if not count))
    order = []
    while ready:
        name = ready.popleft()
        order.append(name)
        for other in sorted(dependents[name]):
            pending[other] -= 1
            if not pending[other]:
                ready.append(other)
    if len(order) != len(sources):
        raise ValueError(f"Import cycle involving: {[n for n, v in pending.items() if v][:12]}")
    return {
        "modules": len(sources),
        "owners": dict(Counter(v["owner"] for v in sources.values())),
        "internal_edges": sum(len(v) for v in dependencies.values()),
        "proof_dependency_to_formal_edges": crossing,
        "external_imports": sorted(external),
        "external_module_existence_checked": False,
        "topological_order": order,
        "lean_build_performed": False,
    }


def generated_config(module_names: list[str]) -> str:
    # Glob.one is selected by an exact module name.  Empty roots are legal;
    # membership and buildability then follow the explicit globs.
    globs = ",\n".join("  " + json.dumps(name) for name in module_names)
    return f'''# Generated source-only view. Do not edit accepted package configurations.
name = "{PACKAGE}"
version = "0.1.0"
defaultTargets = ["{LIBRARY}"]
weakLeanArgs = ["-M2048", "-DElab.async=false"]

[leanOptions]
autoImplicit = false
warningAsError = true

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.35.0"

[[lean_lib]]
name = "{LIBRARY}"
srcDir = "src"
roots = []
defaultFacets = ["leanArts"]
allowImportAll = true
globs = [
{globs}
]
'''


def prepare(repo: Path) -> tuple[Path, dict]:
    sources, private_manifest = collect_sources(repo)
    graph = check_graph(sources)
    project = repo / "formalization/lean"
    if (project / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise ValueError("The source toolchain does not match Lean v4.35.0.")
    original_lock = json.loads((project / "lake-manifest.json").read_text())
    lock = dict(original_lock)
    lock["name"] = PACKAGE
    lock["packages"] = [p for p in original_lock["packages"] if p["name"] != "d27_proof_deps"]
    if any(p.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", p.get("rev", ""))
           for p in lock["packages"]):
        raise ValueError("Every external dependency must have an exact Git revision.")
    mathlib = next(p for p in lock["packages"] if p["name"] == "mathlib")
    if mathlib["inputRev"] != "v4.35.0":
        raise ValueError("The Mathlib lock does not match v4.35.0.")
    view = repo / ".source-build"
    marker = view / "source-map.json"
    if view.is_symlink() or (view / "src").is_symlink():
        raise ValueError("The generated workspace and source directory must not be symlinks.")
    if view.exists() and any(view.iterdir()):
        if not marker.is_file() or json.loads(marker.read_text()).get("schema") != SCHEMA:
            raise ValueError("Refusing to overwrite an unrecognized .source-build directory.")
    view.mkdir(exist_ok=True)
    # A recognizable marker permits preparation to be resumed after interruption.
    marker.write_text(json.dumps({"schema": SCHEMA, "preparation_complete": False}) + "\n")
    destinations = set()
    for entry in sources.values():
        target = view / entry["destination"]
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.is_symlink() or not target.resolve().is_relative_to((view / "src").resolve()):
            raise ValueError(f"Generated target escapes the source view: {target}")
        shutil.copyfile(repo / entry["source"], target)
        if digest(target.read_bytes()) != entry["sha256"]:
            raise ValueError(f"Copy verification failed for {target}")
        destinations.add(target.relative_to(view).as_posix())
    extras = {p.relative_to(view).as_posix() for p in (view / "src").rglob("*.lean")} - destinations
    if extras:
        raise ValueError("The generated source view has stale modules. Remove .source-build "
                         f"and prepare again. Examples: {sorted(extras)[:5]}")
    config = generated_config(sorted(sources))
    parsed = tomllib.loads(config)
    assert parsed["lean_lib"][0]["globs"] == sorted(sources)
    assert parsed["lean_lib"][0]["roots"] == []
    (view / "lakefile.toml").write_text(config)
    (view / "lean-toolchain").write_bytes((project / "lean-toolchain").read_bytes())
    (view / "lake-manifest.json").write_text(json.dumps(lock, indent=2) + "\n")
    report = {
        "schema": SCHEMA,
        "preparation_complete": True,
        "toolchain": TOOLCHAIN,
        "library": LIBRARY,
        "schema_sources": SCHEMA_SOURCES,
        "original_lock_sha256": digest((project / "lake-manifest.json").read_bytes()),
        "dependency_lock": lock,
        "private_manifest_source_count": private_manifest["counts"]["private_sources"],
        "graph": graph,
        "sources": dict(sorted(sources.items())),
    }
    marker.write_text(json.dumps(report, indent=2) + "\n")
    return view, report


def check_lock(view: Path, expected: dict) -> None:
    actual = json.loads((view / "lake-manifest.json").read_text())
    signature = lambda lock: {p["name"]: (p.get("url"), p.get("rev"))
                              for p in lock["packages"]}
    if signature(actual) != signature(expected):
        raise ValueError("Lake changed dependency revisions in the generated workspace. "
                         "Do not treat that build as the pinned-source reproduction.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--prepare-only", action="store_true", help="Generate and inspect the source view only (default).")
    mode.add_argument("--build", action="store_true", help="Explicitly fetch dependencies and compile the source view.")
    parser.add_argument("--no-mathlib-cache", action="store_true", help="Skip Mathlib's cache getter; Lake will build missing dependencies.")
    parser.add_argument("--threads", type=int, choices=(1, 2), default=2, help="LEAN_NUM_THREADS setting, not a hard compiler-process limit.")
    parser.add_argument("--lake", default="lake", help="Lake executable used with --build.")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    try:
        view, report = prepare(repo)
        graph = report["graph"]
        print(f"Prepared {graph['modules']} modules in {view}")
        print(f"Sources: {graph['owners']}; internal import graph is acyclic.")
        print("Preparation checks copied bytes and internal imports. External modules "
              "and Lake configuration elaboration await a real build.")
        if not args.build:
            print("No Lean compiler, dependency download, or proof build was run.")
            return 0
        executable = shutil.which(args.lake)
        if executable is None:
            raise ValueError("Lake was not found. Install the pinned Lean v4.35.0 toolchain "
                             "separately, then rerun with --build. Preparation is complete.")
        env = dict(os.environ)
        env["LEAN_NUM_THREADS"] = str(args.threads)
        print(f"LEAN_NUM_THREADS={args.threads}; compiler arguments include -M2048 and "
              "-DElab.async=false. This is not an OS-level process or memory limit.")
        commands = []
        if not args.no_mathlib_cache:
            commands.append([executable, "exe", "cache", "get"])
        commands.append([executable, "--wfail", "build", LIBRARY + ":leanArts"])
        for command in commands:
            print("Running:", " ".join(command), flush=True)
            subprocess.run(command, cwd=view, env=env, check=True)
            check_lock(view, report["dependency_lock"])
        print("The requested source build exited successfully. Historical byte-bound "
              "acceptance and a fresh axiom audit are separate checks.")
        return 0
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"Source-build error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
