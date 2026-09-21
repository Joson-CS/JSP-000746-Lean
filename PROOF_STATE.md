# JSP-000746 Proof State

## 当前阶段

已完成命题的精确定义、`18 → n ≥ 18` 形式化归约、有限 Boolean/CNF 编码、
确定性 DIMACS 导出及所有语义桥梁。CaDiCaL 3.0.1 已证明实际导出的
`certificates/core.cnf` 为 UNSAT，并生成 `certificates/core.lrat`。Mathlib 的
`lrat_proof` 已读取这两个实际磁盘文件，重放证书并产生 Lean kernel 检查的
空子句推导。该推导现已正式连接到 `coreCNF`、`Finite18`、`HoldsFrom18` 和
正整数无限图表述。

项目锁定 Lean `v4.34.0` 与 Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`。

## 原命题与已报告的加强版本

Erdős Problem #895 的区间表述是：是否存在 `N`，使每个 `n ≥ N` 以及每个
顶点集为 `{1, ..., n}` 的 triangle-free graph，都含有三个 independent
vertices `a, b, a + b`？

Lean 中原来的“充分大”命题是：

```lean
def EventuallyHolds : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HoldsAt n
```

公开问题记录称 Ben Barber 通过 SAT 验证了更强的阈值：对所有 `n ≥ 18`
成立。这个加强版本是：

```lean
def HoldsFrom18 : Prop :=
  ∀ n : ℕ, 18 ≤ n → HoldsAt n
```

来源：

- [Erdős Problem #895](https://www.erdosproblems.com/895)
- [Justin Sun Prize catalog: JSP-000746](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#jsp-000746--must-every-triangle-free-graph-on-the-integers-have-three-independent-vertices-one-equal-to-the-sum-of-the-other-two)

## Lean 顶点类型

```lean
abbrev Vertex (n : ℕ) := Set.Icc (1 : ℕ) n
```

因此 `v : Vertex n` 是一个自然数及其证明
`1 ≤ (v : ℕ) ∧ (v : ℕ) ≤ n`。这直接表示 `{1, ..., n}`，没有把 `0`
错误地当作问题顶点，也没有采用模加法。

对 additive triple `a, b, c`：

- `a ≥ 1` 和 `a ≤ n` 来自 `a.property`；
- `b ≥ 1` 和 `b ≤ n` 来自 `b.property`；
- `c = a + b`，而 `c ≤ n` 来自 `c.property`，所以自动得到 `a + b ≤ n`；
- 因 `a,b ≥ 1`，等式 `c = a + b` 自动推出 `c ≠ a` 与 `c ≠ b`；
- `a ≠ b` 不能从正性和加法等式自动推出，定义通过“三元素 independent
  finset”的 cardinality 条件明确要求它。

## Mathlib `SimpleGraph` API 选择

本项目直接复用以下 Mathlib 定义/API：

- `SimpleGraph (Vertex n)`：无向、无自环的简单图；
- `G.CliqueFree 3`：triangle-free；
- `G.IsIndepSet s`：`s.Pairwise (fun v w ↦ ¬ G.Adj v w)`；
- `G.IsNIndepSet 3 s`：`s` independent 且 `s.card = 3`；
- `G.comap e`：沿嵌入 `e` 拉回邻接关系；
- `SimpleGraph.induce`：Mathlib 中也是 `comap` 的包装；
- `SimpleGraph.CliqueFree.comap`：triangle-free 性沿包含/限制保持。

## 核心定义

精确的 additive independent triple 定义为：

```lean
def IsAdditiveIndependentTriple {n : ℕ} (G : SimpleGraph (Vertex n))
    (a b c : Vertex n) : Prop :=
  vertexValue c = vertexValue a + vertexValue b ∧
    G.IsNIndepSet 3 {a, b, c}
```

`G.IsNIndepSet 3 {a, b, c}` 同时表达：

1. `{a,b,c}` 的任意两个不同顶点均不邻接；
2. `{a,b,c}` 的 cardinality 是 `3`，所以三个顶点确实互异。

固定 `n` 的完整结论是：

```lean
def HoldsAt (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Vertex n),
    G.CliqueFree 3 → HasAdditiveIndependentTriple G
```

## `n = 18` 有限核心

```lean
def Finite18 : Prop :=
  ∀ G : SimpleGraph (Vertex 18),
    G.CliqueFree 3 → HasAdditiveIndependentTriple G
```

`Finite18` 本身仍是核心 proposition；它现已由无参数 theorem
`finite18_proved : Finite18` 证明。

## 已证明的归约

`initialSegmentEmbedding hn : Vertex 18 ↪ Vertex n` 保持自然数标签不变。
对 `G : SimpleGraph (Vertex n)`，`G.comap (initialSegmentEmbedding hn)` 恰是
把 `G` 限制到 `{1, ..., 18}` 后得到的图。

已经由 Lean kernel 检查的 theorem statement 是：

```lean
theorem finite18_implies_holdsFrom18
    (h18 : ∀ G : SimpleGraph (Vertex 18),
      G.CliqueFree 3 → HasAdditiveIndependentTriple G) :
    ∀ n : ℕ, 18 ≤ n →
      ∀ G : SimpleGraph (Vertex n),
        G.CliqueFree 3 → HasAdditiveIndependentTriple G := by
  -- proved in JSP000746/Reduction.lean
```

证明先用 `CliqueFree.comap` 得到前 18 个顶点上的 triangle-free graph，应用
`h18`，再沿同一嵌入把 `a,b,c` 送回原图。嵌入保持整数标签、邻接关系和
finset cardinality，所以加法等式及三点 independence 都保持。

另外已证明两个 statement-fidelity wrapper：

```lean
theorem holdsFrom18_implies_eventuallyHolds
    (h : HoldsFrom18) : EventuallyHolds

theorem finite18_implies_positiveInfiniteStatement
    (h18 : Finite18) : PositiveInfiniteStatement
```

其中无限图的顶点类型为：

```lean
abbrev PositiveVertex := Set.Ici (1 : ℕ)
```

第二个 theorem 把正整数上的无限 triangle-free graph 限制到前 18 个正整数，
应用 `Finite18`，再把所得 additive independent triple 嵌回无限图。

## 有限 Boolean/CNF 编码

`JSP000746/SATEncoding.lean` 独立于 `SimpleGraph` 数学表示建立：

```lean
abbrev EdgeVar := {p : SATVertex × SATVertex // p.1 < p.2}
abbrev Assignment := EdgeVar → Bool
structure Literal where
  edge : EdgeVar
  positive : Bool
abbrev Clause := List Literal
abbrev CNF := Finset Clause
```

端点按 `<` 排序，因此每个无序二元组只产生一个 edge variable。CNF 使用
`Finset Clause`，因为 clause 的排列顺序没有逻辑意义，并且会自动去除重复。

两类约束为：

- 对每个 `a < b < c`，triangle-free clause 是
  `¬ab ∨ ¬ac ∨ ¬bc`；
- 对每个 `a < b` 且 `a+b ≤ 18`，no-independent-additive-triple clause 是
  `ab ∨ a(a+b) ∨ b(a+b)`。

交换 `a,b` 的重复由 `a < b` 消除。项目还显式构造了
`additiveTriples : Finset (Finset SATVertex)`，使用 `Finset.image` 再次去重。

以下数值已由 Lean 的可判定有限计算和证明实际核验：

```lean
theorem edgeVar_count : Fintype.card EdgeVar = 153
theorem triangleIndex_count : Fintype.card TriangleIndex = 816
theorem additiveTriples_count : additiveTriples.card = 72
theorem triangleFreeClauses_count : triangleFreeClauses.card = 816
theorem additiveTripleClauses_count : additiveTripleClauses.card = 72
theorem coreCNF_count : coreCNF.card = 888
```

这些检查使用普通 `decide`，没有调用 SAT solver。

## Boolean 层与数学层的桥梁

`assignmentOfGraph G` 把每条数学边编码为对应 `EdgeVar` 的 Boolean 值，并已
证明 `true`/`false` 分别等价于数学层的 adjacency/non-adjacency。

核心 correctness theorem 是：

```lean
theorem assignmentOfGraph_satisfies_core (G : SimpleGraph SATVertex)
    (htriangle : G.CliqueFree 3)
    (hno : ¬HasAdditiveIndependentTriple G) :
    Satisfies (assignmentOfGraph G) coreCNF
```

因此未来只需取得 `coreCNF` 的受信 UNSAT 证明，即可通过：

```lean
theorem coreCNF_unsat_implies_finite18
    (hunsat : Unsatisfiable coreCNF) : Finite18
```

进入现有数学层，再由 reduction theorem 得到所有目标表述。

## 确定性 DIMACS 层

`JSP000746/DIMACS.lean` 完全不依赖 `Finset` 的内部遍历顺序。它先用
`List.ofFn` 固定顶点列表 `[1,...,18]`，再用嵌套 list traversal 构造：

- `orderedEdges`：按端点 `(u,v)` 的 lexicographic order，`u < v`；
- `orderedTriangleIndices`：按 `(a,b,c)` 的 lexicographic order，
  `a < b < c`；
- `orderedAdditiveIndices`：按 `(a,b)` 的 lexicographic order，
  `a < b` 且 `a+b ≤ 18`。

边的 DIMACS 编号就是其在 `orderedEdges` 中的零基位置加一。因此
`(1,2)` 为 1，`(1,18)` 为 17，`(2,3)` 为 18，最后 `(17,18)` 为 153。
编号类型本身限制为：

```lean
abbrev DIMACSVar := {i : ℕ // 1 ≤ i ∧ i ≤ 153}
```

`edgeIndexEquiv : EdgeVar ≃ DIMACSVar` 给出正反双射，`edgeToIndex` 与
`indexToEdge` 是公开映射。Lean 已证明：

```lean
theorem orderedEdges_length : orderedEdges.length = 153
theorem orderedEdges_nodup : orderedEdges.Nodup
theorem orderedEdges_complete : orderedEdges.toFinset = Finset.univ
theorem edgeToIndex_injective : Function.Injective edgeToIndex
theorem orderedEdges_indices :
  orderedEdges.map edgeToIndex = (List.range 153).map (· + 1)
```

确定的 clause 顺序是先 816 个 `triangleClause`，再 72 个
`additiveClause`；两个区段内部使用上面的 index lexicographic order。
每个 triangle clause 内 literal 顺序为 `¬ab, ¬ac, ¬bc`，每个 additive
clause 内为 `ab, a(a+b), b(a+b)`。Lean 已证明两个 ordered index list 完整、
无重复，并证明：

```lean
def orderedCoreCNF : List Clause :=
  orderedTriangleIndices.map triangleClause ++
    orderedAdditiveIndices.map additiveClause

theorem orderedCoreCNF_length : orderedCoreCNF.length = 888
theorem orderedCoreCNF_toFinset : orderedCoreCNF.toFinset = coreCNF
```

正 literal 序列化为 `+edgeToIndex`，负 literal 序列化为
`-edgeToIndex`。`DIMACSLiteral.toInt_ne_zero` 和
`DIMACSLiteral.toInt_abs_bounds` 在 Lean 中证明了没有 DIMACS variable 0，
且绝对值位于 `1..153`。

## DIMACS 语义桥梁

`assignmentToDIMACS` 与 `dimacsToAssignment` 沿 `edgeIndexEquiv` 双向搬运
Boolean valuation，并已证明互逆。主要语义 theorem 为：

```lean
theorem satisfies_orderedCoreCNF_iff_exportedDIMACS (σ : Assignment) :
  SatisfiesOrdered σ orderedCoreCNF ↔
    SignedDIMACSSatisfies (assignmentToDIMACS σ) exportedDIMACSFormula

theorem exportedDIMACS_unsat_implies_coreCNF_unsat
    (hunsat : SignedDIMACSUnsatisfiable exportedDIMACSFormula) :
  Unsatisfiable coreCNF

theorem coreCNF_unsat_iff_exportedDIMACS_unsat :
  Unsatisfiable coreCNF ↔
    SignedDIMACSUnsatisfiable exportedDIMACSFormula
```

这里的 `exportedDIMACSFormula : List (List Int)` 正是 renderer 写入各 clause
行的 Lean 值，而不是一个与输出脱节的第二份编码。`renderCoreDIMACS` 在其前面
加严格 header `p cnf 153 888`。可执行导出器为
`scripts/ExportDIMACS.lean`。

当前生成文件：

```text
certificates/core.cnf
SHA-256: 260b7c50fac4fcc4525f7253eb37a8750bf744cff5bb41e92a314cdea1ccab45
```

`scripts/ValidateDIMACS.ps1` 从磁盘重新读取并独立解析该文件，确认 153 个实际
出现的 variables、888 个 clauses、每个 clause 恰有 3 个 literal 并以 `0`
终止、无 variable 0、绝对值不超过 153、无空 clause、无重复 literal、无
tautological clause；同时确认前 816 行全为 negative triangle clauses，后
72 行全为 positive additive clauses。

## LRAT certificate 与 kernel verification

使用官方 CaDiCaL 3.0.1 source 构建的可执行文件对 `core.cnf` 求解，结果为
`UNSATISFIABLE`（正常退出码 20）。完整输出保存在
`certificates/cadical-core.log`，未经人工编辑的证明保存在
`certificates/core.lrat`。

```text
CaDiCaL version    3.0.1
source tag/commit  rel-3.0.1 / c60730422e758ef1cebe7aeddf2dda31c996bf04
executable         D:\Users\admin\Desktop\JSP-000746\tools\cadical-3.0.1\build-windows\cadical.exe
executable SHA-256 5055464418a38820e31ae2e02229e03345b749bb254b4c582c473b059625a574
```

```text
core.cnf  SHA-256 260b7c50fac4fcc4525f7253eb37a8750bf744cff5bb41e92a314cdea1ccab45
core.lrat SHA-256 2f8729bd57e5ee6d24292e2b51fc72afad884bedf5234b808615568fe9bac582
core.lrat size    218950 bytes
```

`JSP000746/LRAT.lean` 使用：

```lean
lrat_proof core_lrat_proof
  (include_str "../certificates/core.cnf")
  (include_str "../certificates/core.lrat")
```

`lrat_proof` 的公开 theorem 是 153 个命题变量上的 reified DNF；文件进一步把
checker 已生成并由 kernel 接受的底层证明公开为：

```text
core_lrat_proof (a₁ ... a₁₅₃ : Prop) :
  <888 个 clause-falsification conjunction 组成的 balanced disjunction>
```

其中 triangle clause `¬e₁ ∨ ¬e₂ ∨ ¬e₃` 对应 disjunct
`e₁ ∧ e₂ ∧ e₃`，additive clause `e₁ ∨ e₂ ∨ e₃` 对应
`¬e₁ ∧ ¬e₂ ∧ ¬e₃`。因此它并不直接具有项目的
`SignedDIMACSUnsatisfiable exportedDIMACSFormula` 类型。底层精确类型是：

```lean
disk_sat_fmla_proof : Sat.Fmla.proof diskSatFormula Sat.Clause.nil
```

为避免一次性归约 888 条子句造成高内存，桥接分层完成：

1. `edgeToVar_val_closed` 证明 lexicographic edge 编号的闭式公式；
2. checker 的公式拆为 816 条 triangle clauses 和 72 条 additive clauses；
3. `diskTriangleClauses_eq_exported` 与
   `diskAdditiveClauses_eq_exported` 分别逐 clause/literal 检查两个分块；
4. `diskSatFormula_eq_exported` 合并两个分块；
5. `exported_sat_fmla_proof` 把空子句推导搬到 `exportedSatFormula`；
6. `satValuationOfDIMACS` 和 literal/clause semantic lemmas 把 Boolean DIMACS
   满足性搬到 Mathlib `Sat.Valuation` 满足性。

最终 theorem 链为：

```lean
theorem exportedDIMACS_unsatisfiable_verified :
  SignedDIMACSUnsatisfiable exportedDIMACSFormula

theorem coreCNF_unsat : Unsatisfiable coreCNF
theorem finite18_proved : Finite18
theorem jsp000746_holdsFrom18 : HoldsFrom18
theorem jsp000746_positiveInfinite : PositiveInfiniteStatement
```

上述证明没有使用 `sorry`、`admit`、自定义 `axiom` 或 `native_decide`。

## Statement-fidelity 风险

1. **三点是否必须互异。** 当前形式化按通常图论含义把“three independent
   vertices”解释为三个互异顶点。因此 `a ≠ b` 被明确要求；它不像
   `a+b ≠ a,b` 那样能由正性自动推出。若原 SAT 编码允许 `a = b`，则必须
   调整定义并重新评估阈值 18。
2. **整数域。** Justin Sun Prize 的标题简写为“on the integers”，但
   Erdős Problem #895 的完整区间版本明确给出 `{1,...,n}`。当前项目依用户
   指定采用正自然数有限区间，而不是全体 `ℤ`。
3. **阈值来源。** `18` 的历史来源仍是公开网页所述的 SAT-assisted personal
   communication；不过本仓库现在已有独立生成并由 Lean kernel 重放的 LRAT
   certificate，因此形式化结论本身不依赖该历史证明材料。
4. **不主张最小性。** `HoldsFrom18` 只说所有 `n ≥ 18` 成立；它没有断言
   `18` 是最小可能阈值。
