theory tri_tet imports Complex_Main
begin

(* 
  also have "... = ": pulls the RHS of the immediately preceeding statement and places it where ...
  is. Better than using hence  "triangle (Suc k) = (Suc k) +  k * (k + 1) div 2"

  last time, we saw the `moreover`, `ultimately` idiom, when we use `also have`, we can use `finally`
  at the end of the statements
*)

(*
  definition of triangle
*)
fun triangle :: "nat \<Rightarrow> nat" where
  "triangle n = (if n=0 then 0 else n + triangle(n-1))"

theorem triangle_theorem: "triangle n = n*(n+1) div 2"
proof (induct n)
  case 0
  thus ?case by auto
next
  case (Suc k)
  hence IH: "triangle k = k * (k + 1) div 2" by blast

  have "triangle (Suc k) = (Suc k) + triangle k" by simp
  (* hence  "triangle (Suc k) = (Suc k) +  k * (k + 1) div 2" using IH by argo  *)
  also have "... =  (k+1) +  k * (k + 1) div 2" using IH by simp
  also have "... = Suc k * (Suc k + 1) div 2" by fastforce

  finally show ?case by blast 
qed

(*
  definition of tetrahedral
*)

fun tet :: "nat \<Rightarrow> nat" where
  "tet n = (if n = 0 then 0 else triangle n + tet (n-1))"

theorem "tet n = (n+2)*(n+1)*n div 6"
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  (*
    can also write 
    hence "tet k =  (k+2)*(k+1)*k div 6" as done in the triangle proof  
  *)
  fix k
  assume IH_TET:"tet k = (k+2)*(k+1)*k div 6"
  have "tet (k+1) = triangle (k+1) + tet k" by auto
  also have "... = (k+1)*(k+2) div 2 + (k+2)*(k+1)*k div 6" using triangle_theorem IH_TET by simp
  also have "... = 3*(k+1)*(k+2) div 6 + (k+2)*(k+1)*k div 6" by linarith
  also have "... = (3*(k+1)*(k+2) + (k+2)*(k+1)*k) div 6"
    by (smt (verit, ccfv_threshold) div_plus_div_distrib_dvd_left dvd_add_triv_right_iff even_mult_iff even_plus_one_iff
        mult.assoc mult_2_right nat_mult_dvd_cancel1 numeral_3_eq_3 numeral_Bit0 zero_less_Suc)
  also have "... = (k+3)*(k+2)*(k+1) div 6"
    by (simp add: add_mult_distrib2 mult.commute)
  also have "... = (Suc k + 2)*(Suc k + 1)*(Suc k) div 6"
    by (metis Suc3_eq_add_3 Suc_eq_plus1 add.commute add_2_eq_Suc')
  finally show ?case try
qed
end

