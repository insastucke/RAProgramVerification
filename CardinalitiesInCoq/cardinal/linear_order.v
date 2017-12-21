Require Import RelationAlgebra.relalg.
Require Import cardinal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section s.

Context `{L: laws} {Hl: BL+CNV<<l} {U: united X} {C: cardinal U} {T: tarski X} {P: pointed X}. 

Lemma card_linear_order n (x: X n n): is_order x -> is_linear x -> 
   (2*card x = card' n * card' n + card' n)%nat. 
Proof. 
  intros Ho Hli.
  rewrite <-card_top, <-card_one.
  rewrite <- Hli.
  rewrite <-kernel_refl_antisym.
  rewrite capC, cardcup.
  rewrite cardcnv. lia. 
Qed. 

End s.
