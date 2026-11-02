# PA06 → A19 正 q 复用地图 001（只读）

记录 UTC：2026-10-30T05:27:17.319876+00:00。正式 writer 为新 Root 01a18842-1cab-7ae3-92b2-24c2adf72528；本文件供 Root 转交 PSTR，不改其任何源码/工作垫，不启动编译。

## 结论与精确目标

A06 原 raw 构树机器已经完整闭合，应复用实际运行与序列化结果，不重写 raw 构树。不等于原 raw-input A19 已获得完整 preprocessor。

在本次所查正式源及私有 Lean 中未找到 `A19MachineControllerClaims.prepare` 或该同名字段。真实现有目标是 `PaperProofs.Structure.LaminarTree.CompactControllerClaims.MachineControllerClaims`，`CompactControllerClaims.lean:228–258`：先存在固定 `preprocessor live : List PackingOp` 及统一常数，再对所有 q/full/initialUsed 量化；:242–248 要求从真正 `controllerInput`、zero heap、`packingInitial` 运行该 preprocessor，满足实际 `DynamicRunCorrect`/成本并产出 `HeapRepresents`。这里不另造 prepare 接口。

## 已证 A06 的真实入口

命名空间统一以 `PaperProofs.Structure.LaminarTree` 为前缀，下列文件均在 `lean/PaperProofs/Structure/`。

| 入口 | 已查到的实际签名/结论与用途 |
|---|---|
| `RawTreePreprocessingClaims.lean:31–32` | `rawIncidenceROM q full = ⟨[N,q] ++ incidence full, [], []⟩`，只有维数和 Nq bit。 |
| `RawTreePreprocessingNat.lean:24–30` | `childrenStart=1649`，`tail = RawCandidateSerializedChildrenRAM.programAt childrenStart ++ RawTreeOutputFinalizeRAM.program`；`program : List PackingOp := RawCandidateTreePrefix.program tail`，**不接受 N/q/full 参数**。 |
| `RawTreePreprocessingCodeBounds.lean:26–39` | `program_length=2089`、`code_length=10450`，含真实编码的5-word HALT；Nat程序与该代码相等见 CostBounds:29–33。 |
| `RawCandidateWorkspaceInit.lean:20–41` | `candidateCount=N+q+1`、`workspaceBase=8*candidateCount*q+16`（源码乘数为 q）；16-op `program` 真实从 raw ROM[0]/[1]读取 N/q，计算维数/地址，写入 heap8 与 count cell。不存在免费 dimensions/tree metadata 输入。 |
| `RawTreePreprocessingStartWord.lean:304–310` | `initialized_entry q full hl` 返回某 clock≤checkerSteps+17 的实际 `PrefixSafe`、`StartReady` 和同 clock Word=Nat.toWord。 |
| `RawTreePreprocessingParentWord.lean:47–54` | `parent_entry q full hq hl` 返回原同程序某 clock≤clockBound 的 PrefixSafe、`Ready` 与同 clock Word=Nat.toWord；不是独立 parent oracle。 |
| `RawTreePreprocessingNat.lean:70–102` | `succeeds q full hq hl : ∃ steps ≤ successClockBound, Output ... (natRun raw program steps natInitial)`；Output:56–62给实际HALT/accept/节点数/序列化长度/每个实际heap输出字。 |
| `RawTreePreprocessingNat.lean:181–202` | `raw_preprocessing q full hq` 对全部正q输入（不额外假Laminar）返回 steps≤16384*treeWork、真实HALT、flag≤1、flag=1 iff Laminar；接受时有上述 Output。 |
| `RawTreePreprocessingA06Closure.lean:22–58` | `all_prefix_safe q full hq count` 覆盖任意 clock；`prefixSafety`；`fullClaims : RawTreePreprocessingClaims.FullClaims`，没有待证前提。 |
| `RawTreePreprocessingWordInterface.lean:94–末` | `fullClaims_of_prefixSafety` 具体选择 constant262144、wordFactor16、同一 program；原 DynamicRunCorrect/总成本/实际 TreeOutputCorrect 全部得到。 |

`workspaceBase` 精确源码为 `8 * (N + q + 1) * q + 16`。

## 实际输出及能复用的归一化树

- `RawTreePreprocessingClaims.lean:65–88`：`serializeROM rom = [rom.input.length, rom.internal.length, rom.children.length] ++ rom.input ++ rom.internal ++ rom.children`。最终 heap 从地址0逐字保存该列表；`register.old=t`、`register.fresh=serialized.length`。**heap0 是 input region 长度，不是 t。**
- 同文件:74–88：`readSerializedROM result.heap = AlgorithmClaims.givenTreeROM q full`，不是只声称树同构。`RawTreeSerialization.lean:115–158` 从实际逐字输出证明解码；:160–169的 `treeOutputCorrect_of_words` 不是免费输出构造。
- `AlgorithmClaims.lean:63–71`：givenTreeROM.input=`[N,q,t] ++ Nq stage incidence ++ tq node incidence`；internal=`t parents（0=none，node+1=some） ++ t degrees`；children为按现有 NodeId/child顺序的零基child IDs。不得混用tag-first capacity表示或把缺父0当root node0。
- `RawTreeSerialization.lean:24–50`：input length=3+Nq+tq，internal length=2t，positive-q Laminar时children length=t−1；总序列化长度=6+Nq+tq+2t+(t−1)。真实尺寸均由该run计算，不是新ROM输入。
- `LaminarNormalize.lean:224–230`：`prepareNormalization` 的 nodes 是 `explicitNodeList`，card稳定排序与 `parentFromList`；:238–248证明order成员/排序。它在 FullClaims 中只作**输出规格**。A06证明实际去重/排序/最小parent/children产生同一 indexed tree，并给 t≤N+q+1；空stage不是节点，重复stage保留时序，q1的singleton/top去重不改节点映射。
- givenTreeROM **没有**预给 cardinality/internal flag/leaf labels/stage/tool-node lookup；`AlgorithmClaims.lean:60–62`明确要求实现计算。A19 `staticMetadata`（CompactControllerClaims:141–156）还要 `[edgeCount],parents,degrees,children,cards,internalFlags,leafLabels,stageNodes,toolNodes`。`IndexedStaticMetadata.buildPositive`（:57–70）是规格构造及已证lookup，不是运行免费primitive。A17实际metadata程序/已交付bridge可继续消费A06已物化数据；本文件不重写A17。

## 仍需接通的真实接口（A06 不是缺口重开）

1. **ROM 尾部与输入适配。** 原A06严格证明 `rawIncidenceROM`；A19 `controllerInput`（CompactControllerClaims:171–174）为 raw 后附 q 个 initialUsed bits，live的 `callInput`（:177–179）为 raw 后附1个 command。要证明A06所读区域在含尾部ROM中同值并保持实际fetch/access，或用实际程序作输入投影。不能凭list前缀直接把A06的完整theorem换ROM。ROM加载成本也从 Nq+2 变为 Nq+q+2。initialUsed必须由真正追加bits初始化持久used区，不在后续每次query重新输入。
2. **同一固定代码和有效续接边界。** A06 standalone FullClaims 最终已HALT，不能把 halted state 当免费重启。`PackingProgramPrefix.lean:51–105` 的 `natRun_append_of_body_prefix`/`natRun_append_first_after_boundary` 可以复用真正body prefix：在旧HALT尚未执行的active边界接下一个body，且重核jump目标与fetch。`RawTreePreprocessingFooterWord.footer_nat_safe`（:139–168）给真实13步footer结束pc=5*whole.length且halted=false，`footer_halts_safe`之后才执行第14步HALT。要从整run导出这个pre-HALT输出边界并在包含后续代码的whole程序上证明Word运行/安全；本次未查到直接交付完整A19此结论的定理。
3. **输出数据/代码加载及堆表示。** A06把given-tree ROM字写在可写heap；A17原given-tree机器读的是 PhysicalROM三region，A19却固定raw-ROM。纯数学 `readSerializedROM` 等式不等于真实机器已把heap免费变ROM。需实际heap读取/复制adapter或已交付runtime bridge，把A06输出接入A17metadata/table并维持帧。A19 final heap header是 `[t,capWords,packedCapacityWords,bits]`，data从物理4开始，原A06序列化从0开始；构建、移动/打包、initialUsed、stage0、failed0、所有metadata须产出真实 `HeapRepresents`，不能只假定布局正确。已有 `PA17_A19QueryBridge_PSTR_MAP_001.md` 可作为query侧的互补地图，冻结/正式状态仍由Root确认。
4. **字宽统一。** A06具体是 `indexWidth 16 N q`，完整 A19只允许一个统一wordFactor。若其他阶段用更大factor，需真实widening/refinement而非直接改A06定理的bits。可复用实际通用 `PaperProofs.Structure.LaminarTree.PackingMachine.natRun_toWord`（PackingWordRefinement.lean:175–179）与 `PaperProofs.Structure.LaminarTree.PA17WordBounds023.fits_mono_bits`（PA17_WordBounds_023.lean:15）；其实际namespace已按源码核对，但仍须选择一致的正式依赖版本并证明组合，不能靠本地图当已证组合。
5. **总成本与峰值地址范围。** A06 `heapWords = workspaceLimit = 8*(N+q+1)*q + 16 + 8*(N+q+1) + 8192`（CostBounds:19、WorkspaceInit:20–22、WorkspaceBounds:20）；standalone费用≤262144*(N+q+1)^2*q，包含ROM/code/zero初始化/真实动态trace及HALT。A19目标heapWords固定为 `4 + packedCapacityWords q capWords bits + indexFactor*(N+q+t+1)`，capWords=`tableWords N q t+q+scratchFactor*(t+1)`（CompactControllerClaims:121–123,238–239）。**A06 standalone上界并不自动落在这个A19 compact heap上界内**；要证明实际地址可装入/复用及清理帧，不能仅把两段时间界相加当空间证明。本预审没有声称已给出该接口的形式化反例，且它不否定A06原目标。所有真实loader/word-generator/translation/packing和输出搬移同样需计费。

q0仍走原A18 direct分支，不能套正q乘q的成本式；N0已在正q A06量词中，不需额外排除。以上五项是复用适配的待接接口，不是要求重新证明已闭合A06，也不是新数学方向。

本文件无实现、无编译/审计宣称，不增加任何主张闭合数。
