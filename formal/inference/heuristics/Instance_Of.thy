theory Instance_Of
  imports "../Inference"
begin

definition just_do_it :: update_modifier where
  "just_do_it t1ID t2ID s new old = (if Updates (get_by_id new t1ID) = [] then Some (replaceAll new (get_by_id new t1ID) (get_by_id new t2ID)) else
                                     if Updates (get_by_id new t2ID) = [] then Some (replaceAll new (get_by_id new t2ID) (get_by_id new t1ID)) else None)"

end