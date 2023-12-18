module Pulse.Checker.Prover

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

module PS = Pulse.Checker.Prover.Substs

include Pulse.Checker.Prover.Base
include Pulse.Checker.Prover.Util

val elim_exists_and_pure (#g:env) (#ctxt:vprop)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
  : T.Tac (g':env { env_extends g' g } &
           ctxt':term &
           tot_typing g' ctxt' tm_vprop &
           continuation_elaborator g ctxt g' ctxt')

val prove
  (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (uvs:env { disjoint g uvs })
  (#goals:vprop) (goals_typing:tot_typing (push_env g uvs) goals tm_vprop)

  : T.Tac (g1 : env { g1 `env_extends` g /\ disjoint g1 uvs } &
           nts : PS.nt_substs &
           effect_labels:list T.tot_or_ghost { PS.well_typed_nt_substs g1 uvs nts effect_labels } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 ((PS.nt_subst_term goals nts) * remaining_ctxt))

val try_frame_pre_uvs (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (uvs:env { disjoint g uvs })
  (d:(t:st_term & c:comp_st & st_typing (push_env g uvs) t c))
  (res_ppname:ppname)

  : T.Tac (checker_result_t g ctxt None)

val try_frame_pre (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (d:(t:st_term & c:comp_st & st_typing g t c))
  (res_ppname:ppname)

  : T.Tac (checker_result_t g ctxt None)

val prove_post_hint (#g:env) (#ctxt:vprop)
  (r:checker_result_t g ctxt None)
  (post_hint:post_hint_opt g)
  (rng:range)
  
  : T.Tac (checker_result_t g ctxt post_hint)
