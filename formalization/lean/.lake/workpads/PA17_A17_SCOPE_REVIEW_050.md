# A17 原范围独立只读审查（050）

结论：就下列已读取源码，未发现原 A17 量词收缩、答案/trace 输入、query scratch 正确性或 VOID card 新前提。049 组装保留原 `AlgorithmClaims.FullGivenTreeClaims`，其 witness 是同一个 038 implementation、wordFactor=32、常数 `2^58`。本报告记录源码范围审查与文末的独立原目标 public 调用结果；root 的全 PA17 公理审计和正式集成仍由对应主线独立签收。

原文采用当前 submission 版本：[laminar.tex:25](D:/STOC投稿/compatibility_structure_research/submission_2026-10-27/manuscript/sections/laminar.tex:25)–50 与 [laminar-proofs.tex:245](D:/STOC投稿/compatibility_structure_research/submission_2026-10-27/manuscript/sections/laminar-proofs.tex:245)–280。下表对照 [AlgorithmClaims](D:/STOC投稿/lean/PaperProofs/Structure/AlgorithmClaims.lean:307) 和 049 组装源码。

| 原字段/范围 | 实际对应及审查结果 |
|---|---|
| 外层实现与常数先于输入 | `049.fullGivenTreeClaims` 无参数，直接构造原 existential；Nat 与 packed 两边均为 `PA17WrappedNatRAM038a.implementation`，不是两个不同实现。040 只放大成本常数，不改变程序、heap、wordFactor 或输入量词。 |
| build、table、capacity/index 空间 | 038c 保留全表 `PhysicalTableCorrect`（原 `(N+1)(q+2)` 个 tag-first slots）、真实零 heap build、全 prefix capacity≤q、capacity bits 与独立 index-word 数界。七个专用 spill 已计入 038 indexWords 和两端实际 wipe；没有免费初始化。 |
| query 原量词与确切答复 | Nat 接口仍量化任意原 `heap`，前提恰为 table correct、leading capacity bound 和原 allocated heap Fits；physical 接口量化任意 `BitVec bits → BitVec bits` heap，仅保留 decoded table correct/capacity bound。返回原 `expectedReply` 的 rank/good/bad/tool 四字段，包括原 `IndexedQuery.query`/`selectEntry`/`selectAt` 选择，而非任意最大工具替代。 |
| arbitrary scratch / VOID | 未要求 scratch 为零、metadata/counts/labels 预先正确、所有 index 字有小的多项式值，或 VOID payload≤node card。原 leading-capacity bound 本来就要求所有 capacity words≤q，因此 VOID payload 可为该原范围内任意值。`PhysicalTableCorrect` 的 tag≤1 是原定义自身已有字段。 |
| rolling | 同一 038 implementation 的 rollingProgram 从真实零 heap 执行，保留原初始 rank、stored row 0、全 prefix capacity 和两个 stage layers 的容量空间界；没有以 rolling 替代完整 table。 |
| ≤N 次请求与 workspace reuse | 038c 调用 016 的实际请求归纳：`PathClaims`/`pathExecute` 每步使用上一次 query 的整个输出 heap；只重置寄存器/PC，未恢复旧 scratch 或重启初始 workspace。量化任意 requests list 且 length≤N，实际强于仅因果实现历史；代价逐次包含完整 query cost。 |
| 真正 packed machine | 045f 三 phase 给原 `PackedPhaseRefines`，包含真实每指令 fetch/access、PC=5·count、末尾 HALT、全部寄存器及每个 allocated logical word 相等、所有 physical prefixes capacity≤q。034 read32/write87 采用真实两词 bit 操作及 safeWrite50；不是 `map .base` 的伪 packing。旧 index 字逐字对应，七 spill 的最终零值由实际 stores 建立。 |
| packed bits / index words | 原界为 `physicalWords*bits ≤ C*width(q)+(indexWords+1)*bits`，indexWords 含七 spill；capacity bit 界与普通 index-word 空间分别陈述。不能将“capacity storage bits”误写为所有代码/ROM/index 总内存仅 `O(work log(q+2))`。 |
| 固定六程序 generator | 035ai 的 witness 是单一固定 `048.generator`，在 `∀ N q t` 之前选择，唯一 ROM 为 `[N,q,t]`。真实 prelude 算 width/bits，真实测长、六段 emission 和 forward copy 写出原 `generatedCode(038,045)`（六 length prefixes、六完整 HALTs），没有目标代码/答案/path/trace ROM。 |
| 所有 eligible dimensions | UCG 结论恰保留 `q>0,t>0,t≤N+q+1`；048 的 fixed L/F≤2^32 已由固定 AST 的 code/factor bounds 消去，不是新的运行输入资格。T 是实际 generatedCode 长度，不是 caller output oracle；H=1024+T+2 是被证明的资源分配，不作为 generator 的输入。 |

费用字段没有遗漏整类工作。Nat `totalBuildCost` 含 ROM/code loading、heap 零初始化、8 个初始寄存器/PC writes、全部 execution 与 HALT；`totalQueryCost` 含每次 stage/used 输入 q+1、代码加载、8、执行/HALT，query scratch 由真实程序重写而不是免费全清零。Packed phase 的代码/trace 是相对 Nat 代码/trace 的常数倍界，须与 Nat 成本组合看；generator 自身另计 ROM 3、完整固定代码、H、8 和真实 dynamic trace，总界 `2^58·work`。不能把这一个常数误称为组合后最小的直接物理费用系数。packing 的 width≤bits 也确保物理零初始化不增加字数数量级。

边界审查：

- A17 本结论是原 positive-q given-tree 范围；q=0 的无树直接分支、显式 incidence 下的构树/laminarity 检查没有被本次 A17 组装冒称完成。
- N=0 未被排除；此时 stages 为 `Fin 1`，只剩 terminal reply，≤N 请求列表只能为空。原 query 仍含该 terminal stage。`LaminarSchedule` 不要求列表非空、集合非空、互异或覆盖所有工具，因此 empty/repeated stages 和 absent tools 均保留；统一 universe/singletons 不依赖工具曾出现。
- terminal stage=N 由原 `terminalReply` 返回；空 compatibility 或没有 compatible unused tool 时，原 `stored_query_bad` / `stored_query_tool_none_iff` 给 bad=0、tool=none。无穷 rank、successor rank 的编码与原 expectedReply 一致，没有换为有限截断 rank。
- 008 的实际 incidence count pass 是 O(qt)，本线未声称其本体实现原文255行所述的 O(t) counting 方法；fresh metadata/labels/counts 的实际重算已在总 query `O((q+1)t)` 内计费。该实现路线差别不改变 theorem 的总 query 上界。

静态 code Fits 的 `(N,q,t)=(0,1,1)` 专门化不是样本运行测试。`035ai.fixed_generator_wordsFit64` 的结论仅为同一份维数无关固定 `packingCode 048.generator` 的字面量 Fits64；044n/o 的 `template_constants` / `generator_constants` 检查整份编译源代码，repeat 情形显式使用 `hchecked.2 0`，所以 N=0 未执行的 loop body 也没有被略过。048d 再证明任意 q>0 时 `bits=32*clog₂(N+q+2)≥64`，对同一固定 code list 作 WordsFit 单调提升。任意 eligible N/q/t 的实际执行、安全、输出和 HALT 则由 `six_checked N q t`、`generator_word`、实际 heap/output bounds 全称建立。这里的 32 是 wordFactor，既不是固定 32-bit 机器，也不是只证明 64-bit 下的一个运行样本。

counter 20 的处理也没有缩小 eligible 输入。044b 的 `addLoop`（以及相同指令块的重复 descent/parent loops）使用 20 作生成器重复计数，body 不把该计数作为 emitted operand 读取；其 bound 可为乘积，不能强迫 counter≤线性 numericScale。046i 的 `queryNumericScope = numericScope.erase 20` 只移除这个“小值不变量”，固定 `query_profile` 仍检查所有表达式 cells 的包含关系；count expression 自身及每个子式仍由 Bmax 约束。046h 对 repeat 的归纳只在 counter 确实属于 small scope 时要求 smallBound；lexical WellScoped、counter 地址<64、StackFits 和真实 `TemplateChecked` 对所有 value≤bound 的义务完全保留。因此没有偷加 q/t 小、N>0、count≤linear scale 等输入限制；full/rolling 的 counter 20 仍在其相应 scope 中。

未发现需要向主线报告的实质范围缺口。上述结论仅涉及 A17 原 given-tree integer-rank/tool-selection 与物理实现目标，不扩大到 A06、A18、A19，亦不宣称有限风险精确优化或实数低阶价格系数比较（原文278–280明确排除）。

本次只读版本 SHA256：049 `f3af9df3c0784818c567a1f5ed22897fceee630b74520b82023c2d1d889a33bb`；035ai `69ae7668f1892e3da229c3baf85e1c65ce0c661ed74f6a4440426ad3aa116287`；原 AlgorithmClaims `bb4d42db2cfa00eee681e748e6a6879bc1f60cd94c71f18f8debd4ecb41d415d`。论文两文件 SHA 分别 `34264488235813d5edf4f3f9ee7b507874d57b03910289742a27266de65a5d37`、`e4349779cd119f9389649e77a9d614996e89382910940d0a6b0b24ee8ecbcb0b`。

只读阶段恢复后再次读取 049/035ai，SHA 与上列记录一致。其时 049 尚只有因 035ai 产品未复制到 026 而发生的 import 失败，本报告未提前写成已编译闭合。随后 root 通知相同 SHA 的 049 strict 已真实 exit 0，才触发下述独立调用。

只读阶段没有修改任何生产 Lean 源码、正式文件或主账，也没有编译。之后仅新增下述 050 独立 consumer 与调用日志；当前没有运行句柄。
## 独立普通 import 调用收据

2026-10-30，收到 root 的 049 strict=0/冻结产品通知后，使用普通 `import Structure.PA17_FullGivenTree_049`（没有 `import all`）运行 [050_Public](D:/STOC投稿/lean/.lake/workpads/PA17_A17_SCOPE_REVIEW_050_Public.lean)。两个无参数、无额外前提的 example 分别直接调用：

```lean
example : AlgorithmClaims.FullGivenTreeClaims :=
  PA17FullGivenTree049.fullGivenTreeClaims

example : AlgorithmClaims.UniformCodeGenerationClaims
    PA17GenerationBounds047.generationConstant 32
    PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs :=
  PA17UniformGenerator035ai.uniformCodeGenerationClaims
```

调用使用 installed Lean 4.35.0，经统一 `ROOT_LEAN_SLOT.ps1`，参数为 `--root=.lake/workpads -DautoImplicit=false -DwarningAsError=true`；实际 LEAN_PATH 为已验证的 package/project/toolchain roots 加 `PA17_FormalBridge_026/lib`。未加 `-o`，未重跑已有 all-owned 或全工程检查。

原会话 **31896 已自然完成，真实进程退出状态 exit_code=0**；[日志](D:/STOC投稿/lean/.lake/workpads/PA17_A17_SCOPE_REVIEW_050_public.log) 明确记录 `EXIT_CODE=0`，外层同样报告 `INDEPENDENT_PUBLIC_EXIT_CODE=0`。两个原目标可由普通 public import 直接消费，不是 `#check`、参数化条件 wrapper 或样本执行测试。

- 049 冻结源 SHA：`f3af9df3c0784818c567a1f5ed22897fceee630b74520b82023c2d1d889a33bb`（启动前已核对）。
- 050 consumer SHA：`3df21d675723b64795c096a368f62fd2ddd32250e390f638eff1ef6a254073c5`。
- 050 调用日志 SHA：`b3a18d029967164c7db64d91c1568673660011b26eb78439a62a4c3d0289c8f2`。

本独立调用确认原类型可消费，不替代 root 尚在执行的全部 PA17 传递公理审计或总协调的正式集成，也不改变本报告对 A06/A18/A19 和 q=0 分支的范围边界。
