theory EFSM_LTL_Inf
imports EFSM
begin

codatatype (sset:'a) stream = SCons (shd:'a) (stl: "'a stream") for
  map: smap
  rel: stream_all2

primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
  "siterate g x = SCons x (siterate g (g x))"
end