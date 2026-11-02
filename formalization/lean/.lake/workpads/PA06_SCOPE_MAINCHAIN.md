# PA06 只读预审：B08 / B09 / B11 / B12

记录 UTC：2026-10-30T05:24:34.304246+00:00。由旧 A06 主线程下属只读代理完成；总协调为新 Root `01a18842-1cab-7ae3-92b2-24c2adf72528`。

本文件只是当前源码与冻结原文的对应预审，不是第二套主张台账，不宣告 S7 全篇终验。本次没有启动编译、全工程构建、公理审计，没有编辑任何正式 Lean、entry、AuditAll、README、主账或官方 receipt。只写本 PA06_SCOPE 私有证据。

## 结论

所审 B08、B09（已授权 first-entry 版）、B11、B12 中，未发现足以否定当前“已闭合”登记的原文范围/量词/比较器缺口。原目标 Props 之外，确实存在无待证性能前提的最终证明；不是只核查 Prop 定义。这里是静态源码审查结论，最终构建、公理、当前整工程指纹及全部 S7 终验仍由新 Root 验收。

已只读计算当前冻结16个英文输入源和 PDF SHA，逐一与 `checks/lean-baseline.json` 相等。该检查没有运行文档/Lean编译。数学冻结版本为用户2026-10-29授权的 B09 first-entry 修订，不能拿旧宽历史原句当当前目标。

## B08：独立全策略 infimum 与真实双向递推

原文 `manuscript/sections/price-proofs.tex:59–75` 先独立定义放松资源 caps、删除非负 correction charges、单次 task-failure 罚金 λ>0 的 G，再给 good/bad 后继和递推。原文 `:98–107` 要求覆盖预写弃任务与失败后收费，反向由 near-optimal 测试及续局逼近，不要求最优达到。

真实 Lean 链：

- `HealthyValue.lean:88–92` 的 `StatisticalInput.healthyPenalty input next available penalty` 是 freshSuffix 上 `Native.availablePenaltyValue`，不是递推定义。保原 experiments/fees；current relaxed contract 只规范放松后的合同。`:121–125` 是先证 finite penalty 下值有限，再转 `healthyPenaltyReal`。
- `AvailableValue.lean:22–27,42–45` 的 `UsesOnly` 仅约束真实 reached allocation 使用 R 中工具，`AvailablePolicy` 仍是原 `Policy input C .uncapped` 子类型；不是预先给 MAP/Markov/成功/finite-cost/终止策略类。
- `AvailableValue.lean:161–167` iInf 包含所有小 Seed 类型、可测空间、概率 law 和原合法策略；`NativePenalty.lean:23–27` objective 为 ENNReal 的真实观察费期望 + λ*risk。无限观察费用比较器仍在 inf 内。
- 不是把 `Type` 宇宙限制作数学策略限制：`NativeSeed.lean:33–69` 将任意 Seed 的每个固定私有随机种子编码成只读 visible-history→action 的 `LegalStrategy`；编码函数参数没有 world/truth/tapes。`:71–98` 可测与逐 clock 同 run/成功。`AvailableValue.lean:117–157` 保原观察费和 risk 的 `penaltyObjective_availableEncoded_eq`，`:178–187` `availablePenaltyValue_le_policy_any_seed` 接受 `Seed : Type*`。因此各宇宙的原随机策略都被同值比较。
- lower 已有 `NativePenaltyHeadLower.lean:26–51` 的任意 seed 原策略目标下界，`:55–65` 还显式覆盖 `AvailablePartialPolicy` 的有限已付费 nonreturn totalization，不臆造无限观察费。`:70–95` 对原 iInf 的完整 lower；`NativeHeadTotalLower.lean:111–123` 只作 stageCount≤1/下一stage分支，无有限成本或终止前提。
- upper 中 `NativeBellmanUpper.lean:29–44` 的 `exists_availablePenaltyObjective_near` 从 iInf_lt_iff 得真实 Seed/law/Policy 见证；`:48–57` 的 `exists_localObjective_near` 同样由独立局部 iInf 得真实测试。这些 hpenalty≠⊤ 只是 paper 中有限实数 λ>0 下选择逼近，不排除无限费用竞争策略。
- `NativeBellmanValueUpper.lean:118–144` 分别选择 local/good/bad 三个 epsilon 近似；有工具时仅有限真实 bad-min 的工具取得（`:140–153`），从未要求无限维策略 infimum 取得。空工具 `:175–207` 用原 abandon 策略承担 λ。
- `NativeBellmanValueUpper.lean:75–99` `bellmanIndependentPolicy` 由真实 headTest/continuation 构造原合法 AvailablePolicy。独立 seed law 在 `NativeBellmanPrivateSeeds.lean:183–184` 为 `localLaw.prod (goodLaw.prod badLaw)`；该源 `:202–238` 证明边际与 pair independence。
- `NativeBellmanExpectation.lean:357–417` 的 `someTool_objective_le` 和 `:419–469` 的 `noTool_objective_le` 无待证性能参数，实际把 all-path `runPenaltyCharge` 和真实同源世界拆分后积分；不是只对抽象 branch 数值作代数。`selectedPolicyCharges_integral` 在 `:282–307`，实际 local correct/wrong 权重及续局账单一起运输。
- `NativeBellmanValueUpper.lean:23–38` 消去任意 epsilon；`:221–234` 的 `currentPenaltyRecursion_head` / `currentPenaltyRecursion` 直接给原 `input.CurrentPenaltyRecursion`，只输入 `input`。`HealthyValue.lean:210–215` 原目标量词是全部 stage/R/实数正 penalty。

**判断：**未发现 B08 通过缩窄随机性、假设 infimum 取得、finite bill 或 MAP 才闭合的差距；correction charges 确实只在 paper 的 lower-bound relaxation 中删除，不误称真实完整 variable bill 等于 G。

## B09：获准 first-entry 范围及旧反例隔离

当前冻结 `price-proofs.tex:78` 精确为 “From every healthy native history at the first entry to stage i, with unused tools R ...”；`:80–84` 保留 future actual observation +一次 eventual failure、合法延迟、弃任务、失败后收费。`checks/b09-first-entry-revision.json` 记录明确用户授权、唯一源码行78变更和旧版归档，当前16源/PDF逐 hash匹配。

- `HistoryPenaltyBridge.lean:363–367` 的 `FirstEntryAt` 是真正首次到该 cursor 的 clock，不能由“当前尚未 write/report”代替。
- `HistoryPenaltyBridge.lean:263–284` 使用 finite-clock native counters 的未来 observation 增量 supremum，保 ENNReal；不是两个无限总费用相减。`historyComparisonCharge` 对原完整 runSuccess 的反面只收一次原罚金，含 nontermination/abandon/旧未执行义务。
- `:404–410` 的事件只有固定 public startup 与任意可测 Seed gate；没有真值/成功/未来观测筛选。`:375–392` 的 `AllocationHealthyBefore` 与更严格 `DeadlineViableBefore` 区分真实及时执行：terminalBarrier 允许旧 pending；currentWindow 需已及时执行。
- `:441–458` 的 `StageEntryHistoryPenaltyBridge` 是更强 allocation-only 比较，保原 current-allocation、任意宇宙 seed、真实 native Policy、所有 measurable gate/0质量/∞罚金。真正健康版 `:465–482` 只把健康条件换为 DeadlineViableBefore。
- `HistorySuffixBridge.lean:89–149` 的具体定理构造实际 `guardedReplayRule` / `replayedSuffixCandidate`，直接调用真实 first-entry seed×suffix world 联合法则 (`:121–123`)、逐seed独立G比较 (`:129–131`) 和原全路径费用/成功支配 (`:142–149`)；不把上述 law/性能作为外部前提。
- `HistorySuffixBridge.lean:155–169` 最终 `stageEntryHistoryPenaltyBridge` 与 `healthyStageEntryHistoryPenaltyBridge` 仅接受 `input`，返回原两个 Props（含 arbitrary uBridge）。终局也有独立 terminal 分支。
- 旧宽版 `HealthyHistoryScope.lean:35–51` 原样保存，允许 current stage 已买 reviews；文件说明 `:6–16` 明确只作旧历史目标。`AllHealthyHistoryPenaltyBridge.firstEntry_projection` 只是宽→窄单向条件定理，不是主正向证明依据。
- `HealthyPrewriteCounterexample.lean:433–451` 的 `exists_prewrite_violation` 真正给正质量 public gate、stage0、DeadlineViable、未 write/report、reviews=n≥1、后续 observation0且原一次failure积分严格低于 fresh G×质量；`:470–477` 直接反驳旧宽 Prop。`HealthyHistoryCounterexample.lean:296–298` 另有写入后具体反例。新正向证明不消费旧宽 Prop；旧反例不反驳 first-entry。

**判断：**未发现当前 first-entry 目标与授权冻结范围不符；不能在论文或宣讲中恢复“任意中途 posterior 历史也 ≥fresh G”的旧宽读法。

## B11/B12：严格短后缀、有限 bad-min、等秩消去

原文 `price-proofs.tex:118–154`：同一 fixed healthy state，∞rank零值；有限rank正系数首项；坏后继按最大rank/同rank最小系数选首项；允许 Gb−Gg 的首项完全相消；异秩 J迭代 log 合成；原 λ-min 最终不活跃。

- 原目标 `PenaltyAsymptotics.lean:33–51` 中 `EqualRankCancellation` 和 `PenaltyAsymptotics` 只陈述同一原 input 所有 stage/next/R 与固定后的渐近，不把递推或性能定义为值。
- `HealthyPenaltyAsymptotics.lean:26–31` 的 `HealthyFiniteLeading input next` 覆盖该严格后缀 **全部** available 与 depth，保原 `suffixCoefficient`。
- `:165–203` 当前一步 `healthyPenalty_finite_step` 唯一归纳性能输入是 `HealthyFiniteLeading input (stage.val+1)`；good缩放、bad有限min、local项和已证精确Bellman在此汇合。
- `:205–222` 的 `healthyFiniteLeading_all` 对 `I.stageCount-next` strong induction，`:213–214` 明确证明 `stageCount-(next+1)<size` 后才取 IH；终局 rank=∞排除有限目标。不是同级R互调用或循环使用当前目标。
- `HealthyBadMinimum.lean:108–169` 的 `badPenaltyReal_leading_minimum_of_shorter` 精确要求严格 next+1 的所有 R 首项，再由真实 `eligible∩available` 有限工具集证明存在 B>0、取最大子rank上的最小系数及整个原 bad inf' 的极限。`:18–40` 最小系数选取只在有限集合；不要求某个工具从某 λ 后永远是实际 value-minimizer。
- 空工具分支 `HealthyPenaltyAsymptotics.lean:87–97,150–163` 真实 bad=λ，badDepth=0、B=1；无限good分支 `:68–74` 使用已证零值，而不非法转换 ∞rank 为 Nat。
- 等秩 `HealthyPenaltyAsymptotics.lean:145–148` 只调用局部 `equalRankLocalTerm_tendsto_zero_of_bad_leading`（原 `PenaltyAsymptotics.lean:56–68`），它只需 bad 的 B>0 首项和资源单调性 0≤Gg≤Gb；没有假设 Gb−Gg 发散或有正首项。
- 异秩 `HealthyPenaltyAsymptotics.lean:126–144` 先由严格后缀得 Gg/o(Gb)，再用真实局部 `localValueReal_iteratedLog_succ_of_tendsto`；其纯解析证明在 `LocalIteratedComposition.lean:44–61`，从 t/ell_b→B>0 独立推出 t→∞ 后组合已证 localLogarithmicPrice，含 badDepth0。
- 外层min `HealthyPenaltyAsymptotics.lean:192–201` 调 `LocalIteratedComposition.lean:78–93`，由 depth≥1 的迭log首项推出 min(λ,bracket)最终等于bracket，非额外假设。
- `HealthyPenaltyAsymptotics.lean:224–228` 的 `penaltyAsymptotics input` 用上述已证 `healthyFiniteLeading_all` 直接闭合原 Prop；全局 `equalRankCancellation input` 在 **其后** `:230–234`，从已证严格下一后缀有限首项提取。前面的有限归纳没有调用这个 globalB11，也没有把整个 `PenaltyAsymptotics` 作为 ih。
- `HealthyInfiniteRank.lean:23–39,49–55` 用真实原 uncapped reference 策略的零观察费/零risk闭合 independent inf=0，接受 `penalty : ENNReal`（含∞），没有 H0/数值资格作假设。

**判断：**B12使用局部B11a而非待证全局B11；原本文关于 cancellation、min selection 和lambda截断的承重论证均有具体形式化证明入口。未发现本次应撤销 B11/B12 闭合状态的范围缺口。

## 非数学缺口与范围边界

1. 旧说明注释有过时“still needs upper construction / remaining proof must supply ...”：`NativePenaltyHeadLower.lean:97–99`、`PenaltyAsymptotics.lean:41–43`、`HistoryPenaltyBridge.lean:486–488` 等。最终闭合声明在后来导入模块，不能仅凭这些旧注释判为证明缺口。可由Root合适时统一改文档，当前预审不编辑正式文件。
2. 这里没有重验局部统计所有库引理、机器复杂度、B24/M08或全论文其他主张；这些由父代理另核。本预审不把统计价格闭合推广为实际算法/Bool TM完成。
3. 没有新数学主张、没有建议扩大模型或修订冻结稿；也没有在私有工作垫提前登记新主张闭合。

## 所审源码 SHA256（恢复复核用）

以下 hash 精确对应本次读取快照；正式集成若改动相关文件，应再核对应点。本段不是官方 receipt。

| 文件（相对 D:/STOC投稿） | SHA256 |
|---|---|
| `compatibility_structure_research/submission_2026-10-27/LEAN_BASELINE.md` | `1355f4038f42c7804dc12886d8f3f32da26457058cac94355504933e9d29e936` |
| `compatibility_structure_research/submission_2026-10-27/checks/lean-baseline.json` | `482ae3a9db46975645836fc33210b3302d68ead2bfe20d9b38bb274976c14d30` |
| `compatibility_structure_research/submission_2026-10-27/checks/b09-first-entry-revision.json` | `9c870a3b5b27704a17b5a5e5bdca3b857e410356d3a88f12a195548181275bc6` |
| `compatibility_structure_research/submission_2026-10-27/manuscript/sections/price-proofs.tex` | `bcdd21ab9ad087387494792ee90951afdd593b14e199f868cd53026f92f0f589` |
| `lean/PaperProofs/Common/HealthyValue.lean` | `e61215d455bac33aff833c7c09537e9668590babff9dee53f8285ad0612ae7af` |
| `lean/PaperProofs/Common/AvailableValue.lean` | `1f50d9ee20ff56cf8ef949e97e7b012f01f70b12905ac103ba1c21bb8a92773c` |
| `lean/PaperProofs/Common/NativePenalty.lean` | `39c1498b099df4b2a249aedc4699cafc4088955d0be18572c183157625008188` |
| `lean/PaperProofs/Common/NativeSeed.lean` | `fa85c9e62509d9fc5270c2e0c99f94d81af9443a2d0b4443eb3b7427054812f6` |
| `lean/PaperProofs/Common/NativePenaltyHeadLower.lean` | `cc95378d0eeabbd159e88baf1e980dbd0919425130ebb890787ea0f2647acee4` |
| `lean/PaperProofs/Common/NativeHeadTotalLower.lean` | `fb1c52b1647d4c772762ac38cdd453da90063515729f475aff6097a39a165479` |
| `lean/PaperProofs/Common/NativeHeadBayes.lean` | `ee71b44c7481d69ebe75e93fb4f563576f8b0111d42409eb2fec2eaab7051a01` |
| `lean/PaperProofs/Common/NativeBellmanUpper.lean` | `c68d407492841eaf789defabf72a5b3fe705bd964f73aa40081f612c78c7b862` |
| `lean/PaperProofs/Common/NativeBellmanValueUpper.lean` | `08f10783b29c8ee16c781b070616defceff9a812a2a751b160b07950f6fe6566` |
| `lean/PaperProofs/Common/NativeBellmanPrivateSeeds.lean` | `02485288f3b2b262159d6e9fd7cef4d8d4b76b38ab2f91bc8fb3137dc542d46f` |
| `lean/PaperProofs/Common/NativeBellmanExpectation.lean` | `bf9c9b2412f33eac54dcefe900ed8df863f97dff9ca32d6f19308f34a3353efd` |
| `lean/PaperProofs/Common/HistoryPenaltyBridge.lean` | `e603aecddb55e819fab3914df0000bb76053c867ba99eb995816f07a02057a03` |
| `lean/PaperProofs/Common/HistorySuffixBridge.lean` | `45379a58e9266421dac4c03bfb3f12365a0f67648c56c4c87e07ce81027e788c` |
| `lean/PaperProofs/Common/HealthyHistoryScope.lean` | `96e9a1a77bda45fda53684db7ad94b473df7e423611bdc1624e08461c2c52c84` |
| `lean/PaperProofs/Common/HealthyHistoryCounterexample.lean` | `cb40fe051181b302db5397d5c6227c316bc529e32c2080a8780a909e1eeb3e9b` |
| `lean/PaperProofs/Common/HealthyPrewriteCounterexample.lean` | `dc28b9a3bc98141e58327db0c5a8b92d7759f9f0757321218a2ac8f322f32b48` |
| `lean/PaperProofs/Common/HealthyPenaltyAsymptotics.lean` | `f03427a342b46221ccc1dffb849fa37d2365c7b162cff4a9065bdb4ba617de64` |
| `lean/PaperProofs/Common/PenaltyAsymptotics.lean` | `6484265fbc316f288026e63e52ca333d2452a2e991f58047399066fc7908423a` |
| `lean/PaperProofs/Common/HealthyBadMinimum.lean` | `4f482f108852ddefb677a29032bf8f22bca41fd37269f8296d7e464ac4811a95` |
| `lean/PaperProofs/Common/HealthyInfiniteRank.lean` | `089f2e1697e19e7fd41d3a24203715295ea0cf62f2509bae72f684c72d13edd8` |
| `lean/PaperProofs/Statistics/LocalIteratedComposition.lean` | `aab326f1cae95171a993c06b6b403ed2b556ddaf848f0cbf97af66b4e757601d` |
