import Valaig.Aig.Basic

namespace Valaig.Aig

variable {aig : Aig}

theorem decls_unique_inputs :
    ∀ {i j} (hi : i < aig.size) (hj : j < aig.size),
      aig.aig.decls[i] matches .atom (.input _) ∧ aig.aig.decls[i] = aig.aig.decls[j] →
      i = j := by
  have := aig.hinputmap.hsurjec
  grind

theorem decls_unique_latches :
    ∀ {i j} (hi : i < aig.size) (hj : j < aig.size),
      aig.aig.decls[i] matches .atom (.latch _) ∧ aig.aig.decls[i] = aig.aig.decls[j] →
      i = j := by
  have := aig.hlatchmap.hsurjec
  grind

theorem decls_unique_atoms :
    ∀ {i j} (hi : i < aig.size) (hj : j < aig.size),
      aig.aig.decls[i] matches .atom _ ∧ aig.aig.decls[i] = aig.aig.decls[j] →
      i = j := by
  intro i j hi hj
  match h : aig.aig.decls[i] with
  | .false => simp
  | .gate _ _ => simp
  | .atom (.input _) => grind only [decls_unique_inputs]
  | .atom (.latch _) => grind only [decls_unique_latches]

theorem inputs_unique :
    ∀ {i j} (hi : i < aig.numInputs) (hj : j < aig.numInputs),
      aig.inputs[i].var = aig.inputs[j].var → i = j := by
  grind

theorem latches_unique :
    ∀ {i j} (hi : i < aig.numLatches) (hj : j < aig.numLatches),
      aig.latches[i].var = aig.latches[j].var → i = j := by
  grind

section

variable {lit : Lit} {symbol : String}
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}
variable {next : Lit} {reset : Option Lit}

theorem addInput_size_ge :
    (aig.addInput symbol).fst.size ≥ aig.size := by
  simp_all [addInput]

@[grind! .]
theorem validIn_addInput (h : lit.validIn aig) :
    lit.validIn (aig.addInput symbol).fst := by
  grind [addInput_size_ge, Lit.validIn]

@[grind! .]
theorem addInput_validIn :
    (aig.addInput symbol).snd.validIn (aig.addInput symbol).fst := by
  simp [addInput, Lit.validIn]

theorem addInput_notInverted :
    ¬(aig.addInput symbol).snd.inverted := by
  simp [addInput]


theorem addLatch_size_ge :
    (aig.addLatch next reset symbol).fst.size ≥ aig.size := by
  simp_all [addLatch]

@[grind! .]
theorem validIn_addLatch (h : lit.validIn aig) :
    lit.validIn (aig.addLatch next reset symbol).fst := by
  grind [addLatch_size_ge, Lit.validIn]

@[grind! .]
theorem addLatch_validIn:
    (aig.addLatch next reset symbol).snd.validIn (aig.addLatch next reset symbol).fst := by
  simp [addLatch, Lit.validIn]

theorem addLatch_not_inverted :
    ¬(aig.addLatch next reset symbol).snd.inverted := by
  simp [addLatch]


theorem addLatch'_size_ge :
    (aig.addLatch' reset symbol).fst.size ≥ aig.size := by
  simp_all [addLatch']

@[grind! .]
theorem validIn_addLatch' (h : lit.validIn aig) :
    lit.validIn (aig.addLatch' reset symbol).fst := by
  grind [addLatch'_size_ge, Lit.validIn]

@[grind! .]
theorem addLatch'_validIn:
    (aig.addLatch' reset symbol).snd.validIn (aig.addLatch' reset symbol).fst := by
  simp [addLatch', Lit.validIn]

theorem addLatch'_not_inverted :
    ¬(aig.addLatch' reset symbol).snd.inverted := by
  simp [addLatch']


theorem addGate_size_ge :
    (aig.addGate rhs0 rhs1 h0 h1).fst.size ≥ aig.size := by
  simp_all [addGate]

@[grind! .]
theorem validIn_addGate (h : lit.validIn aig) :
    lit.validIn (aig.addGate rhs0 rhs1 h0 h1).fst := by
  grind [addGate_size_ge, Lit.validIn]

@[grind! .]
theorem addGate_validIn:
    (aig.addGate rhs0 rhs1 h0 h1).snd.validIn (aig.addGate rhs0 rhs1 h0 h1).fst := by
  simp [addGate, Lit.validIn]
  have (r : Std.Sat.AIG.Entrypoint Aig.Atom) := r.ref.hgate
  grind

end

end Valaig.Aig
