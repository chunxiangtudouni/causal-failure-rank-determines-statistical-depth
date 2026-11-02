# Causal Failure Rank Determines Statistical Depth

本仓库包含论文 **Causal Failure Rank Determines Statistical Depth** 的 Lean 4 形式化证明。作者为 **Zhaochen Zang（臧昭晨）、Zhongnian Li（李仲年）、Ziyue Jin（金子越）、Xinzheng Xu（许新征）**，共同单位为中国矿业大学计算机科学与技术学院／人工智能学院。通讯作者为李仲年，邮箱为 [zhongnianli@gmail.com](mailto:zhongnianli@gmail.com)。

[论文与 Lean 对应表](docs/current-paper-correspondence.md) · [英文说明](README.md) · [复现指南](ARTIFACT.md)

形式化覆盖因果分配博弈、层状兼容结构的紧凑算法、固定图统计价格律、保留分配与星形实例、控制器计算保证及独立的付费扩展。`RootPaper014` 快照的 **253/253 项登记主张已闭合，S7 原稿对应审查已完成**，验收日期为 2026 年 11 月 2 日。

## 阅读论文与证明

通过[对应表](docs/current-paper-correspondence.md)查找定理的 Lean 入口。[完整登记表](docs/paper-to-lean.md)保留全部 253 项原始 ID、冻结稿锚点及证明绑定。[PaperProofs.lean](formalization/lean/PaperProofs.lean) 是公共导入入口。本仓库只分发形式化工程、依赖与检查记录，论文文件单独提供。

B23 的计算保证由 `PaperProofs.Common.Native.B23PaperClosure.full_paper_claims` 闭合，L01 的紧凑价格控制器由 `PaperProofs.Structure.LaminarTree.L01PaperClosure.full_paper_claims` 闭合。它们各自证明论文级 `FullPaperClaims`，保留原输入位长、数值额度与资源条件。

原 S7 验收通过源码和 PDF 哈希绑定冻结原稿，仓库保留原验收记录。当前论文调整了题目和论述结构，[对应表](docs/current-paper-correspondence.md)通过稳定标签和真实定理入口连接两个版本。

## 检查与复现

在仓库根目录运行以下源码清单检查，需要 Python 3.11 以上版本。

```console
python scripts/review_snapshot.py
```

该命令核对源码哈希与历史验收元数据，不编译 Lean，也不覆盖冻结收据。另行持有哈希匹配的冻结论文时，可以按[复现指南](ARTIFACT.md)进行 S7 对应重放；该步骤还需要 `ripgrep`。

全部 3,833 个证明依赖源码均直接保存在 Git 中，不分发预编译依赖包，也不需要 Git LFS。先准备统一源码构建工作区。

```console
python scripts/build_from_source.py --prepare-only
```

该工作区保留模块原名，将正式证明与本地依赖统一交给 Lake 按导入顺序构建。Lean 与 Mathlib 固定为 `v4.35.0`，其他依赖由清单锁定。完整构建命令、资源控制与公理审计步骤见[复现指南](ARTIFACT.md)。准备依赖后，可在 VS Code 中打开生成的工作区阅读证明。

## 引用与许可

引用信息见 [CITATION.cff](CITATION.cff)。公开地址为 [GitHub 仓库](https://github.com/chunxiangtudouni/causal-failure-rank-determines-statistical-depth)。

本仓库尚未授予项目许可证。源码构建和历史验收记录的读取方式见[复现指南](ARTIFACT.md)。
