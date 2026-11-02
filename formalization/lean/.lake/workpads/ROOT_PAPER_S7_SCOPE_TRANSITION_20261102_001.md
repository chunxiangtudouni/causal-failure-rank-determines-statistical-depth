# S7 的论文范围转换与最终验收入口（准备记录）

状态：**仅准备，未闭合 B23/L01，未修改正式主账、收据、S7 矩阵或旧 Lean 定义。** 当前251/253、S7=false。依据 Root 中用户直接指令“以论文定义为主，实现证明论文中所写的必须项，达到该要求即可，不必要的统统砍掉”，见 `ROOT_HUMAN_PAPER_SCOPE_20261102_001.json`。

本记录解决的是最终验收的类型与原文绑定，避免成本包齐全后又沿旧强化机器目标重做。数学、统计、风险、完整费用、原资源资格与原输入域保持；显式 BoolTM0/ISA/磁带布局等可选强化另行保留。

## 两条主张必须保留的论文内容

- **B23，price-proofs.tex:294–300：** posterior odds 的有理数产品/比较；整数比较与有理阈值、quota、资格算法；原输入位长和数值 native quotas 的计算成本；不足 caps 返回原 sufficient check 失败；不暗增固定合同资源、不假设 real KL oracle、不声称 poly(log H)。计算结果必须用于同一个原控制器，保原 H0/caps、失败和不返回路径完整收费、原风险和费用结论。
- **L01，prices.tex:127–152：** 实际 laminar preprocessing 与原 depth/critical indices；原 channel 输入上的精确符号 leading coefficient；原 N,q≥1 时的 O(Nqt) 组合 heads 工作加树构造；capacity table 实现同一个因果上界脚本，原观察、target、mismatch handles、实际价格和 caps 不变；不用 KL 数值 oracle 或指数 tool-state 展开。实际 TABLE 记录与统计计算的保存、重放和位成本必须付费，不能借不同 tie 的 generic run 相等来转移。

当前已验收 Scalar、TABLE、Symbolic、Prep 四个 producer 包。Root 的 B23 Core 与 L01 JointWordRun 连接已严格通过，保同一原 policy 与同一实际 P 堆。**尚缺 Reference/TABLE final cost connection 的完整工作覆盖与总费用，故这些 core 不是全目标证明。**

## 已查明可直接复用的 S7 机制

`PStar_S7_GLOBAL_verify_002.py` 已支持通过 `--matrix/--census/--receipt/--manifest` 选择新的编号验收包；它从所选矩阵的 `immutable_open_target_spec_snapshot` 读取精确目标类型。最终不必放宽或绕过它的类型/收据/原文覆盖检查。

最终新快照应只对 B23/L01 采用独立、明确的 **paper-aligned 完整规格及其 canonical formal theorem**，并在同一 scope-transition 记录中保存旧强化目标名/完整声明/旧快照出处。旧 `PStar_S7_GLOBAL_ORIGINAL_TARGET_SPECS_001.json`、旧矩阵及012/013收据不改；旧 `RationalControllerComputationClaims` 和 `CompactPrice.FullClaims` 源码不改，不宣称它们已被新 paper theorem 证明。

其他已接受目标的规格、原文锚点、量词/比较器和证明出处保持，已有251项语义覆盖与已验收全篇预审复用。新矩阵需按当前唯一 `DEPENDENCIES.md` 逐字段绑定，所有 deferred slot 的新 receipt epoch 绑定到同一实际新全体收据，同时保留原 acceptance provenance。不能机械地把旧epoch当新epoch。

## 成本包齐全后执行的有限步骤

1. 读完整最终成本端点，核对实际带计费算法的 value projection、schedule/工作覆盖、原语实现、原数据生产/复制、总路径费用和域。操作表费用有界与原算法结果正确的并列结论不足以代替该连接。只补这一真实缺口，不开发 VM/编译器。
2. 在新 canonical formal modules 中给出 B23/L01 paper 完整规格及无额外待证前提的完整定理。先 ordinary typed consumer 绑定精确规格；固定代码/常数在原输入之前，所有原风险、费用和资源结论均为结果。
3. 复用既有项目 proof-dependency/安装流程接入必要新增闭包和真实已冻产品；父件保留，不重编父件。新 formal umbrella/audit 只补新增入口，严格编译和依赖公理检查使用 Guard003/global2/M2048。
4. 核对新成本及新类型的论文对应后，透明改 B23/L01 两条主账映射及范围说明，生成新的匹配收据。取消强化要求本身不计证明闭合；新收据不能伪称旧 BoolTM0 规格已证。
5. 构建新的编号矩阵、规格快照和 manifest，复用既有16源/253 ID/22环境/131段原文语义预审；对新 B23/L01 做必要增量对应。执行一次最终 S7 readiness 检查及 Root 语义签收，旧已验收结果不反复重跑。完整构建/公理审计/包来源和实际 immutable logs 必须与所选新收据匹配。

本准备记录没有未来成功 hash、没有预填实际 exit0，没有新增 formal theorem，也不使 S7 变为完成。只有完成上述实际验收后才推进正式计数和最终目标状态。
