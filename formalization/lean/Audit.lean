module

import PaperProofs

-- Inspect the actual axioms used by each completed theorem.
-- Standard Lean foundations such as propext, Classical.choice and
-- Quot.sound are expected; sorryAx must never appear in a finished proof.
#print axioms PaperProofs.square_expansion
#print axioms PaperProofs.linear_bound
#print axioms PaperProofs.finite_card_bound
