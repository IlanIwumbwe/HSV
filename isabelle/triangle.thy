theory triangle imports Complex_Main
begin

(*
  definition of triangle

  also have "... = ": pulls the RHS of the immediately preceeding statement and places it where ...
  is. Better than using hence  "triangle (Suc k) = (Suc k) +  k * (k + 1) div 2"

  last time, we saw the `moreover`, `ultimately` idiom, when we use `also have`, we can use `finally`
  at the end of the statements
*)
fun triangle :: "nat \<Rightarrow> nat" where
  "triangle n = (if n=0 then 0 else n + triangle(n-1))"

theorem "triangle n = n*(n+1) div 2"
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

end

