# Problem 06: 雅可比矩阵行列式积分

## 导入的库

```lean
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Convolution
```

## 设置选项

```lean
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
```

## 打开命名空间

```lean
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology Matrix
```

## 主要内容

### 变量声明

- `{n : ℕ} [NeZero n]` - 非零自然数n

### 定义

#### 雅可比矩阵

```lean
noncomputable def jacobianMatrix (f : Fin (n-1) → (EuclideanSpace ℝ (Fin n)) → ℝ)
    (φ : (EuclideanSpace ℝ (Fin n)) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if h : i.val < n - 1 then
      fderiv ℝ (f ⟨i.val, h⟩) x (EuclideanSpace.single j 1)
    else
      fderiv ℝ φ x (EuclideanSpace.single j 1)
```

定义了一个n×n的雅可比矩阵，前n-1行是函数f的偏导数，最后一行是函数φ的偏导数。

### 引理

#### 1. 行列式的余子式展开

```lean
lemma det_cofactor_expansion (M : Matrix (Fin n) (Fin n) ℝ) :
    M.det = ∑ j : Fin n, (-1)^(n + j.val) * M (Fin.last (n-1)) j *
      (M.submatrix (Fin.castSucc ·) (fun k => if k.val < j.val then k else k.succ)).det
```

**说明**: 矩阵行列式按最后一行展开的公式（未证明）。

#### 2. C²函数的分部积分

```lean
lemma integration_by_parts_C2
    (f : Fin (n-1) → (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (φ : (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hφ : ContDiff ℝ ⊤ φ)
    (hφ_supp : HasCompactSupport φ) :
    ∫ x, (jacobianMatrix f φ x).det = 0
```

**说明**: 对于C²可微函数和具有紧支集的光滑函数，雅可比矩阵行列式的积分为0（未证明）。

#### 3. 磨光函数逼近

```lean
lemma mollifier_approximation
    (f : Fin (n-1) → (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hf : ∀ i, ContDiff ℝ 1 (f i))
    (V : Set (EuclideanSpace ℝ (Fin n)))
    (hV : IsOpen V) (hV_bounded : Bornology.IsBounded V) :
    ∃ f_m : ℕ → Fin (n-1) → (EuclideanSpace ℝ (Fin n)) → ℝ,
      (∀ m i, ContDiff ℝ ⊤ (f_m m i)) ∧
      (∀ i j, Tendsto (fun m => ∫ x in V, ‖fderiv ℝ (f_m m i) x (EuclideanSpace.single j 1) -
                                           fderiv ℝ (f i) x (EuclideanSpace.single j 1)‖)
                      atTop (𝓝 0))
```

**说明**: C¹函数可以用光滑函数序列逼近，并且导数也在L¹范数意义下收敛（未证明）。

### 主定理

```lean
theorem determinant_integral_zero
    (f : Fin (n-1) → (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hf : ∀ i, ContDiff ℝ 1 (f i))
    (φ : (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hφ : ContDiff ℝ ⊤ φ)
    (hφ_supp : HasCompactSupport φ) :
    ∫ x, (jacobianMatrix f φ x).det = 0
```

**定理内容**: 对于C¹可微函数f和具有紧支集的光滑函数φ，雅可比矩阵行列式的积分为0。

**证明思路**:
1. 首先利用φ的紧支集性质，找到一个包含支集的球
2. 使用磨光函数逼近将C¹函数逼近为光滑函数序列
3. 对每个逼近函数，利用C²情形的结果得到积分为0
4. 通过极限过程，证明原函数的积分也为0

**证明状态**: 主要框架已完成，但极限部分的详细证明留作`sorry`。
