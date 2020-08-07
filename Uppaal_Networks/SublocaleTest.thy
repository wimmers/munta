theory SublocaleTest
  imports Main
begin

\<comment> \<open>The final locale that defines a function which I will want to execute\<close>
locale FinalThing =
  fixes somefunc :: "nat \<Rightarrow> nat"
  assumes "somefunc 42 = 1337"
begin
definition "final_result = somefunc 42"
end

\<comment> \<open>Some other locale that I can easily interpret directly\<close>
locale DetailThing =
  fixes someval :: "nat"
  assumes "someval = 1336"

\<comment> \<open>Going from DetailThing to FinalThing\<close>
context DetailThing
begin
fun thefunc :: "nat \<Rightarrow> nat" where
  "thefunc _ = someval + 1"
end
sublocale DetailThing \<subseteq> DetailSub: FinalThing
  where somefunc = thefunc
  \<comment> \<open>defines final_result_impl = DetailSub.final_result\<close>
  using DetailThing_axioms DetailThing_def FinalThing.intro thefunc.simps by auto

global_interpretation DetailThing
  where someval = "1334 + 2"
  defines final_result_impl = DetailSub.final_result
  and the_func_impl = thefunc
  by (standard, simp)

export_code the_func_impl in SML \<comment> \<open>works because of the "defines final_result_impl = FinalThing.final_result"\<close>
export_code final_result_impl in SML \<comment> \<open>doesn't work despite the "defines the_func_impl = thefunc"\<close>

end