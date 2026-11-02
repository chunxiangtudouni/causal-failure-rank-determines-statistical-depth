"""Read-only registered proof-dependency guard compatibility draft (stdlib only).

Call verify_registered_packages immediately before AND after every official
build/audit and require identical full fingerprints. This binds frozen audited
proofs; it does not rerun Lean or infer a proof from a source/header/receipt.
"""
from __future__ import annotations

import hashlib
from graphlib import CycleError, TopologicalSorter
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import tomllib

SHA = re.compile(r"[0-9a-f]{64}\Z")
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")
KERNEL_SUFFIXES = SUFFIXES[:3]
PRODUCER_STATUSES = frozenset((
    "COMPLETE_ACTUAL_ORIGIN_AUDIT_COVERAGE_1956_SOURCE_PIN_BOUND",
    "COMPLETE_ACTUAL_ORIGIN_AUDIT_COVERAGE_SOURCE_PIN_BOUND",
))
STD3 = frozenset(("propext", "Classical.choice", "Quot.sound"))
CONFIG = frozenset(("lakefile.toml", "lake-manifest.json", "lean-toolchain"))
_UNPINNED = object()


class ProofDependencyError(ValueError):
    """A registered proof package fails a binding or structural invariant."""


def _need(condition, message):
    if not condition:
        raise ProofDependencyError(message)


def _unique_object(pairs):
    out = {}
    for key, value in pairs:
        _need(key not in out, f"duplicate JSON key: {key}")
        out[key] = value
    return out


def _json(raw):
    return json.loads(raw.decode("utf-8-sig"), object_pairs_hook=_unique_object)


def _rel(value):
    _need(isinstance(value, str) and value and "\\" not in value, f"non-POSIX relative path: {value!r}")
    p = PurePosixPath(value)
    _need(not p.is_absolute() and p.as_posix() == value, f"non-canonical relative path: {value!r}")
    for part in p.parts:
        _need(part not in (".", "..") and not part.endswith((".", " ")), f"path traversal/alias: {value}")
        _need(not any(c in part for c in ':*?<>|\"\x00'), f"invalid path component: {value}")
        _need(part.split(".")[0].upper() not in {"CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10))}, f"reserved path component: {value}")
    return p


def _plain(path):
    try:
        st = path.lstat()
    except FileNotFoundError as exc:
        raise ProofDependencyError(f"missing bound path: {path}") from exc
    _need(not stat.S_ISLNK(st.st_mode) and not (getattr(st, "st_file_attributes", 0) & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400)), f"symlink/reparse point forbidden: {path}")
    return st


def _inside(root, rel):
    q = root.joinpath(*_rel(rel).parts)
    _need(q.resolve().is_relative_to(root.resolve()), f"path escapes root: {rel}")
    cursor = root
    _plain(cursor)
    for part in _rel(rel).parts:
        cursor /= part
        if cursor.exists() or cursor.is_symlink():
            _plain(cursor)
    return q


def _module(value):
    _need(isinstance(value, str) and MODULE.fullmatch(value), f"unsupported module identity: {value!r}")
    return value


def _imports(value):
    _need(isinstance(value, list), "imports must be a list")
    return list(dict.fromkeys(_module(m) for m in value))


def _origin(value):
    _need(isinstance(value, str) and value, "missing frozen_origin")
    return value.replace("\\", "/").casefold()


def _basename(value):
    return value.replace("\\", "/").rsplit("/", 1)[-1]


def _pointer(value, pointer):
    _need(isinstance(pointer, str) and pointer.startswith("/"), f"invalid JSON pointer: {pointer!r}")
    try:
        for part in pointer[1:].split("/"):
            part = part.replace("~1", "/").replace("~0", "~")
            value = value[int(part)] if isinstance(value, list) else value[part]
    except (KeyError, IndexError, ValueError, TypeError) as exc:
        raise ProofDependencyError(f"unresolved JSON pointer {pointer}") from exc
    return value


def _header_imports(raw):
    """Lean 4.35 Module/Syntax: optional module/prelude; repeated one-module imports.

    Header-only scanner, with nested Lean comments. Unsupported quoted module
    names fail closed. Body strings/comments are not lexed as header imports.
    """
    text = raw.decode("utf-8-sig")
    pos = 0

    def word():
        nonlocal pos
        while True:
            while pos < len(text) and text[pos].isspace():
                pos += 1
            if text.startswith("--", pos):
                end = text.find("\n", pos + 2)
                pos = len(text) if end < 0 else end + 1
            elif text.startswith("/-", pos):
                depth = 1
                pos += 2
                while depth and pos < len(text):
                    if text.startswith("/-", pos):
                        depth += 1
                        pos += 2
                    elif text.startswith("-/", pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
                _need(depth == 0, "unterminated header comment")
            else:
                break
        m = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", text[pos:])
        if not m:
            return None
        pos += len(m[0])
        return m[0]

    token = word()
    if token == "module":
        token = word()
    if token == "prelude":
        token = word()
    found = []
    while token is not None:
        if token == "public":
            token = word()
        if token == "meta":
            token = word()
        if token != "import":
            break
        target = word()
        if target == "all":
            target = word()
        found.append(_module(target))
        token = word()
    return list(dict.fromkeys(found))


def _nonnegative_audit(obj):
    """Check proof-policy fields, not unrelated historical statuses/counters."""
    if isinstance(obj, dict):
        for key, value in obj.items():
            if key in {"new_axioms", "forbidden_dependencies"}:
                _need(type(value) is int and value == 0, f"nonzero/invalid {key}")
            if key == "new_axiomInfo_allowed":
                _need(value is False, "new axiomInfo allowed")
            if key in {"allowed_axioms", "allowed"}:
                if isinstance(value, list) and all(isinstance(v, str) for v in value):
                    _need(set(value) <= STD3, f"non-Std3 audit allowance: {value}")
            _nonnegative_audit(value)
    elif isinstance(obj, list):
        for value in obj:
            _nonnegative_audit(value)


def _receipt_record(obj, source_basename):
    """Select the bound actual auditor, never a neighbouring public check."""
    if isinstance(obj, list):
        matches = []
        for r in obj:
            if not isinstance(r, dict):
                continue
            source = r.get("source", r.get("path", ""))
            source = source.get("path", "") if isinstance(source, dict) else source
            if isinstance(source, str) and _basename(source) == source_basename:
                matches.append(r)
        _need(len(matches) == 1, f"receipt has no unique actual audit record: {source_basename}")
        return matches[0]
    _need(isinstance(obj, dict), "audit receipt must be object or audit-record array")
    if isinstance(obj.get("checks"), list):
        return _receipt_record(obj["checks"], source_basename)
    if any(k in obj for k in ("actual_exit", "exit", "returncode")):
        return obj
    if isinstance(obj.get("audit"), dict):
        return _receipt_record(obj["audit"], source_basename)
    raise ProofDependencyError(f"cannot resolve actual audit receipt: {source_basename}")


def _check_exit(record):
    exits = [record[k] for k in ("actual_exit", "exit", "returncode") if k in record]
    _need(exits and all(type(x) is int and x == 0 for x in exits), "actual audit receipt is not exit 0")
    _nonnegative_audit(record)


def _required_product_suffixes(row, where):
    """Absent metadata retains the old five-object contract; never infer a downgrade.

    Explicit kernel triples bind frozen proof-kernel products only. They do not
    assert fresh source reconstruction or availability of executable IR caches.
    """
    _need(isinstance(row, dict), f"invalid product inventory row: {where}")
    if "required_product_suffixes" not in row:
        return SUFFIXES
    value = row["required_product_suffixes"]
    _need(isinstance(value, list) and all(isinstance(s, str) for s in value),
          f"invalid required_product_suffixes: {where}")
    kinds = set(value)
    _need(len(kinds) == len(value) and kinds in (set(KERNEL_SUFFIXES), set(SUFFIXES)),
          f"required_product_suffixes must be standard kernel triple or five: {where}")
    return KERNEL_SUFFIXES if kinds == set(KERNEL_SUFFIXES) else SUFFIXES


def _compatible_field(row, generic, legacy, where):
    """Read either spelling; reject conflicting dual metadata rather than prefer one."""
    _need(generic in row or legacy in row, f"missing {generic}/{legacy}: {where}")
    if generic in row:
        _need(legacy not in row or row[generic] == row[legacy], f"conflicting {generic}/{legacy}: {where}")
        return row[generic]
    return row[legacy]


def _product_pin_map(pins, required, where):
    _need(isinstance(pins, list) and len(pins) == len(required), f"incomplete product binding: {where}")
    found = {}
    for pin in pins:
        _need(isinstance(pin, dict) and pin.get("suffix") in required and pin["suffix"] not in found,
              f"invalid/duplicate product pin kind: {where}")
        _need(isinstance(pin.get("sha256"), str) and SHA.fullmatch(pin["sha256"]), f"invalid product SHA pin: {where}")
        origin = _origin(pin.get("path"))
        _need(origin.endswith(pin["suffix"]), f"product frozen path/kind mismatch: {where}")
        found[pin["suffix"]] = (pin["sha256"], origin)
    _need(set(found) == set(required), f"incomplete kernel/product binding: {where}")
    return found


def verify_registered_packages(project: Path, normal_fingerprint: dict[str, str]) -> dict:
    """Return exactly summary/fingerprint/graph; raise on any inconsistent package.

    normal_fingerprint MUST be freshly computed by the official verifier on each
    call. Official frontier sources are never reread here. The caller must compare
    complete fingerprints before/after EACH build or audit, and retain this result.
    """
    project = Path(project).resolve()
    _need(project.is_dir(), "missing Lean project")
    _plain(project)
    _need(isinstance(normal_fingerprint, dict) and all(isinstance(k, str) and isinstance(v, str) and SHA.fullmatch(v) for k, v in normal_fingerprint.items()), "invalid normal fingerprint")
    fingerprint = dict(normal_fingerprint)
    graph = {}
    hashed_files = 0
    hashed_bytes = 0

    def read_actual(p, expected=_UNPINNED, size=_UNPINNED, capture=True):
        nonlocal hashed_files, hashed_bytes
        st_before = _plain(p)
        _need(stat.S_ISREG(st_before.st_mode), f"not a regular file: {p}")
        h = hashlib.sha256()
        chunks = []
        length = 0
        with p.open("rb") as f:
            while chunk := f.read(1024 * 1024):
                h.update(chunk)
                length += len(chunk)
                if capture:
                    chunks.append(chunk)
        st_after = _plain(p)
        _need((st_before.st_size, st_before.st_mtime_ns, st_before.st_ino) == (st_after.st_size, st_after.st_mtime_ns, st_after.st_ino), f"file changed while hashing: {p}")
        actual = h.hexdigest()
        _need(expected is _UNPINNED or isinstance(expected, str) and SHA.fullmatch(expected) and actual == expected, f"SHA drift: {p}")
        _need(size is _UNPINNED or type(size) is int and size == length, f"size drift: {p}")
        key = p.relative_to(project.parent).as_posix()
        _need(key not in fingerprint or fingerprint[key] == actual, f"normal/package fingerprint mismatch: {key}")
        fingerprint[key] = actual
        hashed_files += 1
        hashed_bytes += length
        return b"".join(chunks) if capture else None

    project_raw = {}
    for filename in CONFIG:
        p = _inside(project, filename)
        key = p.relative_to(project.parent).as_posix()
        _need(key in normal_fingerprint, f"normal fingerprint omits project config: {key}")
        project_raw[filename] = read_actual(p, normal_fingerprint[key])
    project_toml = tomllib.loads(project_raw["lakefile.toml"].decode("utf-8-sig"))
    project_lake = _json(project_raw["lake-manifest.json"])
    registry = _json(read_actual(_inside(project, "ProofDeps/proof-packages.json")))
    _need(type(registry.get("version")) is int and registry["version"] == 1 and isinstance(registry.get("packages"), list) and registry["packages"], "invalid/empty proof registry")
    registered = registry["packages"]
    _need(all(isinstance(r, dict) and set(r) == {"name", "path", "manifest", "sha256"} for r in registered), "unsupported proof registry entry")
    names = [r["name"] for r in registered]
    _need(all(isinstance(n, str) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", n) for n in names) and len(names) == len(set(n.casefold() for n in names)), "duplicate/invalid package name")
    roots = [str(_rel(r["path"])) for r in registered]
    _need(len(roots) == len(set(x.casefold() for x in roots)) and all(x.startswith("ProofDeps/") for x in roots), "duplicate/non-ProofDeps package path")
    _need(all(not (a.casefold() + "/").startswith(b.casefold() + "/") for a in roots for b in roots if a != b), "nested registered packages forbidden")
    required = project_toml.get("require", [])
    _need(isinstance(required, list), "invalid project require table")
    local_requires = [r for r in required if "path" in r]
    _need(len(local_requires) == len(registered), "unregistered/missing local require")
    path_entries = [r for r in project_lake.get("packages", []) if r.get("type") == "path"]
    _need(len(path_entries) == len(registered), "native Lake local-package set differs")
    summaries = []
    all_modules = set()

    for reg in registered:
        pkg = _inside(project, reg["path"])
        _need(pkg.is_dir(), f"missing registered package {pkg}")
        require = [r for r in local_requires if r.get("name") == reg["name"]]
        _need(len(require) == 1 and set(require[0]) == {"name", "path"} and require[0]["path"] == reg["path"], "registered require name/path/config deviation")
        native = [r for r in path_entries if r.get("name") == reg["name"]]
        _need(len(native) == 1, "native Lake package name differs")
        native = native[0]
        _need(native.get("dir") == reg["path"] and native.get("configFile") == "lakefile.toml" and native.get("manifestFile") == "lake-manifest.json" and native.get("inherited") is False and native.get("copy") is False and native.get("scope", "") == "", "native Lake path package registration deviation")
        expected_files = {}
        expected_fold = {}

        def declare(rel, role):
            rel = _rel(rel).as_posix()
            _need(rel.casefold() not in expected_fold, f"duplicate/case-colliding package asset: {rel}")
            expected_fold[rel.casefold()] = rel
            expected_files[rel] = role
            return _inside(pkg, rel)

        manifest_path = declare(reg["manifest"], "manifest")
        manifest = _json(read_actual(manifest_path, reg["sha256"]))
        for key in ("sources", "formal_frontier", "configuration", "evidence_assets", "coverage", "entry"):
            _need(key in manifest, f"package manifest omits {key}")
        _need(isinstance(manifest["sources"], list) and isinstance(manifest["formal_frontier"], list), "invalid source inventories")
        config = manifest["configuration"]
        _need(isinstance(config, list) and {r["path"] for r in config} == CONFIG and len(config) == 3, "package configuration must bind exactly three native config files")
        config_raw = {}
        for r in config:
            config_raw[r["path"]] = read_actual(declare(r["path"], "configuration"), r["sha256"], r["bytes"])
        _need(tomllib.loads(config_raw["lakefile.toml"].decode("utf-8-sig")) == {"name": reg["name"], "buildDir": "artifacts", "leanLibDir": "lean"}, "prebuilt package config must have exactly name/buildDir/leanLibDir; no lean_lib/require/hooks")
        pkg_lake = _json(config_raw["lake-manifest.json"])
        _need(pkg_lake.get("name") == reg["name"] and pkg_lake.get("packages") == [], "proof package has native dependencies/name deviation")
        _need(config_raw["lean-toolchain"] == project_raw["lean-toolchain"], "proof package toolchain differs")
        module_rows = {}
        module_folds = set()
        source_pins = {}
        staged_products = {}
        required_products = {}
        for r in manifest["sources"]:
            m = _module(r["module"])
            _need(not m.startswith("PaperProofs.") and m != "PaperProofs", "partial PaperProofs artifact/source overlay forbidden")
            _need(m.casefold() not in module_folds, f"duplicate/case-colliding module: {m}")
            module_folds.add(m.casefold())
            module_rows[m] = r
            src = r["source"]
            _need(src["path"] == m.replace(".", "/") + ".lean", f"source path/module identity mismatch: {m}")
            raw = read_actual(declare(src["path"], "source"), src["sha256"], src["bytes"])
            _origin(src["frozen_origin"])
            source_pins[m] = src["sha256"]
            graph[m] = _imports(r["imports"])
            _need(_header_imports(raw) == graph[m], f"actual source-header import DAG mismatch: {m}")
            required = _required_product_suffixes(r, f"manifest {m}")
            required_products[m] = required
            products = r["products"]
            _need(isinstance(products, list) and len(products) == len(required), f"not required products: {m}")
            staged_products[m] = {}
            for p in products:
                prefix = "artifacts/lean/" + m.replace(".", "/")
                _need(p["path"].startswith(prefix), f"product module identity mismatch: {m}")
                suffix = p["path"][len(prefix):]
                _need(suffix in required and suffix not in staged_products[m], f"invalid/duplicate product kind: {m}")
                read_actual(declare(p["path"], "product"), p["sha256"], p["bytes"], capture=False)
                _origin(p["frozen_origin"])
                staged_products[m][suffix] = p
            _need(set(staged_products[m]) == set(required), f"missing required kernel/product kind: {m}")
        for r in manifest["formal_frontier"]:
            m = _module(r["module"])
            _need(m.startswith("PaperProofs.") and m.casefold() not in module_folds, f"invalid/duplicate formal frontier origin: {m}")
            module_folds.add(m.casefold())
            module_rows[m] = r
            required_products[m] = _required_product_suffixes(r, f"formal frontier {m}")
            _need(r["source"] == m.replace(".", "/") + ".lean", f"formal source path/module mismatch: {m}")
            _inside(project, r["source"])
            key = project.name + "/" + r["source"]
            _need(key in normal_fingerprint and normal_fingerprint[key] == r["sha256"], f"formal frontier not bound by fresh normal fingerprint: {m}")
            source_pins[m] = r["sha256"]
            graph[m] = _imports(r["imports"])
        _need(not all_modules & set(source_pins), "origin belongs to multiple proof packages")
        all_modules.update(source_pins)
        entry = _module(manifest["entry"])
        _need(entry in staged_products, "entry is not an original staged module")
        evidence = {}
        evidence_raw = {}
        evidence_parsed = {}
        for r in manifest["evidence_assets"]:
            _need(r["path"].startswith("evidence/"), "evidence may not add source/runtime-object overlays outside evidence/")
            p = declare(r["path"], "evidence")
            raw = read_actual(p, r["sha256"], r["bytes"])
            origin = _origin(r["frozen_origin"])
            _need(origin not in evidence, f"duplicate frozen evidence origin: {r['frozen_origin']}")
            evidence[origin] = r
            evidence_raw[origin] = raw

        def evidence_ref(r, parse=True):
            origin = _origin(r["path"])
            _need(origin in evidence and evidence[origin]["sha256"] == r["sha256"], f"missing/wrong bound audit evidence: {r['path']}")
            if parse and origin not in evidence_parsed:
                evidence_parsed[origin] = _json(evidence_raw[origin])
            value = evidence_parsed[origin] if parse else None
            return _pointer(value, r["json_pointer"]) if parse and "json_pointer" in r else value

        cov_ref = manifest["coverage"]
        coverage = _json(read_actual(declare(cov_ref["path"], "coverage"), cov_ref["sha256"]))
        _need(coverage.get("complete_actual_origin_coverage") is True and coverage.get("uncovered_origins") == [], "actual origin coverage is incomplete")
        _need(coverage.get("source_origin_sha256") == source_pins, "coverage source-origin pins differ from complete staged/frontier set")
        _nonnegative_audit(coverage)
        _need(coverage.get("new_axioms") == coverage.get("forbidden_dependencies") == 0, "normalized audit policy fails")
        producer_ref = coverage["producer_certificate"]
        producer_rel = _rel(producer_ref["path"]).as_posix()
        _need(producer_rel in expected_files and expected_files[producer_rel] == "evidence", "producer certificate must be a bound evidence asset")
        producer_asset = next(r for r in manifest["evidence_assets"] if r["path"] == producer_rel)
        _need(producer_asset["sha256"] == producer_ref["sha256"], "producer certificate hash differs")
        producer = _json(evidence_raw[_origin(producer_asset["frozen_origin"])])
        _nonnegative_audit(producer)
        _need(isinstance(producer.get("status"), str) and producer["status"] in PRODUCER_STATUSES, "producer is not a complete actual-collector certificate")
        _need(set(producer.get("allowed_axioms", [])) == STD3, "producer allowance is not Std3")
        public_root = producer["original_public_root"]
        _need(public_root["module"] == entry and public_root["public_premises"] == 0 and public_root["unchanged"] is True, "unconditional original public root differs")
        origin_rows = producer["origins"]
        _need(isinstance(origin_rows, list), "producer origin inventory missing")
        origins = {r["module"]: r for r in origin_rows}
        _need(len(origins) == len(origin_rows) and set(origins) == set(source_pins), "producer origin coverage mismatch/duplicate")
        _need(evidence_ref(producer["set_proof"]["target_original_DAG"]) == {m: graph[m] for m in source_pins}, "frozen original DAG differs from package source graph")
        audits = producer["audit_evidence"]
        ids = [a["id"] for a in audits]
        _need(len(ids) == len(set(ids)) and ids, "duplicate/empty collector evidence set")
        audits = dict(zip(ids, audits))
        for id_, a in audits.items():
            _need(type(a.get("actual_exit")) is int and a["actual_exit"] == 0 and a.get("new_axiomInfo_allowed") is False and set(a.get("allowed_axioms", [])) == STD3, f"collector policy/exit differs: {id_}")
            scope = a["collector_scope"]
            owners = scope["complete_original_module_ids"]
            _need(len(owners) == len(set(owners)) == scope["complete_owner_count"] and set(scope["owned_source_pins"]) == set(owners), f"collector owned-source inventory inconsistent: {id_}")
            _need(all(SHA.fullmatch(h) for h in scope["owned_source_pins"].values()), f"invalid collector source pin: {id_}")
            credited = scope["actual_DAG_origins_credited"]
            _need(len(credited) == len(set(credited)) == scope["credited_count"] and set(credited) == set(owners) & set(source_pins), f"collector credit is not real owner intersection: {id_}")
            _need(all(scope["owned_source_pins"][m] == source_pins[m] for m in credited), f"collector owner/source mismatch: {id_}")
            evidence_ref(a["audit_source"], parse=False)
            evidence_ref(a["actual_log"], parse=False)
            evidence_ref(a["frozen_manifest"])
            selected = evidence_ref(a["actual_receipt"])
            selected = _receipt_record(selected, _basename(a["audit_source"]["path"]))
            _check_exit(selected)
            if "source_sha256" in selected:
                _need(selected["source_sha256"] == a["audit_source"]["sha256"], f"receipt auditor source pin differs: {id_}")
            if isinstance(selected.get("source"), dict) and "sha256" in selected["source"]:
                _need(selected["source"]["sha256"] == a["audit_source"]["sha256"], f"receipt source object pin differs: {id_}")
            if isinstance(selected.get("log"), dict) and "sha256" in selected["log"]:
                _need(selected["log"]["sha256"] == a["actual_log"]["sha256"], f"receipt log object pin differs: {id_}")
            if "log_sha256" in selected:
                _need(selected["log_sha256"] == a["actual_log"]["sha256"], f"receipt log pin differs: {id_}")
            minimum = a["minimum_replay_entry"]
            inv_ref = minimum["frozen_source_product_inventory"]
            if "json_pointers" in inv_ref:
                base_ref = {k: v for k, v in inv_ref.items() if k != "json_pointers"}
                obj = evidence_ref(base_ref)
                for ptr in inv_ref["json_pointers"]:
                    _pointer(obj, ptr)
            else:
                evidence_ref(inv_ref)
        for m, r in origins.items():
            _need(r["source_sha256"] == source_pins[m], f"producer source pin mismatch: {m}")
            refs = r["audit_evidence_ids"]
            _need(refs and len(refs) == len(set(refs)), f"uncovered/duplicate origin references: {m}")
            _need(all(id_ in audits and m in audits[id_]["collector_scope"]["actual_DAG_origins_credited"] for id_ in refs), f"origin is not owned by its real collector: {m}")
            inv = evidence_ref(_compatible_field(r, "unique_source_and_products", "unique_source_and_five_products", m))
            _need(inv["module"] == m and inv["source_sha256"] == source_pins[m] and _imports(inv["imports"]) == graph[m], f"inventory origin/source/import mismatch: {m}")
            _need(inv["product_variant_count"] == len(inv["product_variants"]) == 1, f"non-unique actual product variant: {m}")
            required = required_products[m]
            _need(_required_product_suffixes(r, f"producer {m}") == required, f"producer/manifest required product kinds differ: {m}")
            _need(_required_product_suffixes(inv, f"inventory {m}") == required, f"inventory/manifest required product kinds differ: {m}")
            actual_pins = _compatible_field(r, "product_pins", "five_product_pins", m)
            actual_map = _product_pin_map(actual_pins, required, f"producer {m}")
            inventory_pins = inv["product_variants"][0]["products"]
            inventory_map = _product_pin_map(inventory_pins, required, f"inventory {m}")
            _need(inventory_map == actual_map, f"producer/inventory product mismatch: {m}")
            if m in staged_products:
                _need(_origin(module_rows[m]["source"]["frozen_origin"]) in {_origin(x) for x in inv["source_candidates"]}, f"staged source frozen origin mismatch: {m}")
                for p in actual_pins:
                    staged = staged_products[m][p["suffix"]]
                    _need(staged["sha256"] == p["sha256"] and _origin(staged["frozen_origin"]) == _origin(p["path"]), f"staged product is not the audited original: {m}{p['suffix']}")
        counts = producer["counts"]
        _need(counts["original_actual_source_DAG_origins"] == counts["union_origins"] == len(source_pins), "producer union count differs")
        for key in ("cached_new_overlap", "uncovered_origins", "duplicate_origin_rows", "source_pin_mismatch", "new_axioms", "forbidden_dependencies"):
            _need(counts.get(key) == 0, f"producer coverage defect: {key}")
        _need(counts["actual_audit_evidence_records"] == len(audits), "producer evidence count differs")

        # Walk only this registered package. No hidden sources/objects or partial
        # PaperProofs tree, even an empty one, may supplement the pinned inventory.
        found = set()
        disk_case = {}
        for folder, dirs, files in os.walk(pkg, followlinks=False):
            for name in dirs + files:
                p = Path(folder) / name
                st = _plain(p)
                rel = p.relative_to(pkg).as_posix()
                _rel(rel)
                _need(rel.casefold() not in disk_case, f"case-colliding on-disk path: {rel}")
                disk_case[rel.casefold()] = rel
                _need(not (rel.casefold() == "artifacts/lean/paperproofs" or rel.casefold().startswith("artifacts/lean/paperproofs/")), "partial PaperProofs artifact directory forbidden")
                if stat.S_ISREG(st.st_mode):
                    found.add(rel)
                else:
                    _need(stat.S_ISDIR(st.st_mode), f"non-file/non-directory asset: {rel}")
        _need(found == set(expected_files), f"missing/extra package assets: missing={sorted(set(expected_files)-found)[:8]} extra={sorted(found-set(expected_files))[:8]}")
        summaries.append({"name": reg["name"], "path": reg["path"], "private_sources": len(manifest["sources"]),
                          "same_identity_products": sum(len(products) for products in staged_products.values()),
                          "legacy_kernel_triple_count": sum(required_products[m] == KERNEL_SUFFIXES for m in staged_products),
                          "formal_frontier": len(manifest["formal_frontier"]),
                          "audited_original_origins": len(origins), "actual_collector_evidence": len(audits),
                          "evidence_assets": len(manifest["evidence_assets"]), "entry": entry,
                          "all_source_object_evidence_hashes_checked": True, "formal_source_rehashes": 0})

    # Project module IDs must be complete; only the actual D27 upstream prefixes
    # Mathlib/Lean/Init are external to this preserved original source graph.
    for m in graph:
        for dep in graph[m]:
            _need(dep in graph or dep.split(".")[0] in {"Mathlib", "Lean", "Init"}, f"missing project source origin: {m} -> {dep}")
    try:
        TopologicalSorter({m: [d for d in deps if d in graph] for m, deps in graph.items()}).prepare()
    except CycleError as exc:
        raise ProofDependencyError(f"original source import cycle: {exc}") from exc
    return {"summary": {"packages": summaries, "package_count": len(summaries), "original_module_count": len(graph),
                        "stream_hashed_files": hashed_files, "stream_hashed_bytes": hashed_bytes,
                        "allowed_axioms": sorted(STD3), "new_axioms": 0, "forbidden_dependencies": 0,
                        "external_payload_hashes_checked_by_guard_not_Lake": True,
                        "requires_equal_fresh_pre_post_fingerprints_for_each_command": True},
            "fingerprint": fingerprint, "graph": graph}
