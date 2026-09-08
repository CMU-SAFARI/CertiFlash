(* Geometry.v: parametric NAND geometry constants for the framework.
   The framework is structured against a GEOMETRY module type with three
   abstract size parameters (pages per block, addressable logical pages, total
   physical blocks) and their positivity assumptions.  An artifact build picks
   a concrete instance; the default below uses small values for fast checking,
   but any module satisfying GEOMETRY can be substituted without re-deriving
   the framework's theorems. *)

Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Module Type GEOMETRY.
  Parameter pages_per_block : nat.
  Parameter addr_space : nat.
  Parameter total_blocks : nat.
  Parameter pages_per_block_pos : pages_per_block > 0.
  Parameter addr_space_pos : addr_space > 0.
  Parameter total_blocks_pos : total_blocks > 0.
End GEOMETRY.

Module DefaultGeometry <: GEOMETRY.
  Definition pages_per_block : nat := 4.
  Definition addr_space : nat := 4.
  Definition total_blocks : nat := 8.
  Lemma pages_per_block_pos : pages_per_block > 0.
  Proof. unfold pages_per_block; lia. Qed.
  Lemma addr_space_pos : addr_space > 0.
  Proof. unfold addr_space; lia. Qed.
  Lemma total_blocks_pos : total_blocks > 0.
  Proof. unfold total_blocks; lia. Qed.
End DefaultGeometry.
