let rec imp__0_iota _3_n =
  imp__4_loop (Scheme.Num (Num.num_of_int 2)) _3_n
  where rec imp__4_loop _5_curr _6_counter =
    if Scheme.is_true
         (Scheme.lt _6_counter (Scheme.Num (Num.num_of_int 2)) Scheme.Nil)
    then
      Scheme.Nil
    else
      Scheme.cons _5_curr
        (imp__4_loop (Scheme.add2 (Scheme.Num (Num.num_of_int 1)) _5_curr)
           (Scheme.sub2 _6_counter (Scheme.Num (Num.num_of_int 1))))
and imp__1_sieve _7_lst =
  let rec imp__8_choose_45pivot _10_lst =
    if Scheme.is_true (Scheme.is_null _10_lst) then _10_lst
    else if
      Scheme.is_true
        (Scheme.eq (Scheme.Num (Num.num_of_int 0)) (Scheme.car _10_lst)
           Scheme.Nil)
    then
      Scheme.cons (Scheme.car _10_lst)
        (imp__8_choose_45pivot (Scheme.cdr _10_lst))
    else
      Scheme.cons (Scheme.car _10_lst)
        (imp__8_choose_45pivot
           (imp__9_do_45sieve (Scheme.car _10_lst)
              (Scheme.sub2 (Scheme.car _10_lst)
                 (Scheme.Num (Num.num_of_int 1)))
              (Scheme.cdr _10_lst)))
  and imp__9_do_45sieve _11_step _12_current _13_lst =
    if Scheme.is_true (Scheme.is_null _13_lst) then _13_lst
    else if
      Scheme.is_true
        (Scheme.eq (Scheme.Num (Num.num_of_int 0)) _12_current Scheme.Nil)
    then
      Scheme.cons (Scheme.Num (Num.num_of_int 0))
        (imp__9_do_45sieve _11_step
           (Scheme.sub2 _11_step (Scheme.Num (Num.num_of_int 1)))
           (Scheme.cdr _13_lst))
    else
      Scheme.cons (Scheme.car _13_lst)
        (imp__9_do_45sieve _11_step
           (Scheme.sub2 _12_current (Scheme.Num (Num.num_of_int 1)))
           (Scheme.cdr _13_lst))
  in
  imp__8_choose_45pivot _7_lst
and imp__2_is_45prime _14_n =
  if Scheme.is_true
       (Scheme.eq (Scheme.Num (Num.num_of_int 0))
          (Scheme.car (Scheme.reverse (imp__1_sieve (imp__0_iota _14_n))))
          Scheme.Nil)
  then
    Scheme.intern "composite"
  else Scheme.intern "prime"
in
imp_loop () where rec imp_loop () = do {
  ignore
    (do {
       ignore (Scheme.display (imp__2_is_45prime (Scheme_read.read ())));
       Scheme.newline ()
     });
  imp_loop ()
};
