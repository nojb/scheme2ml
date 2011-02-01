do {
  let rec __fact =
    Scheme.Lambda
      (fun args ->
         match args with
         [ Scheme.Cons {Scheme.car = __n; Scheme.cdr = Scheme.Nil} ->
             if Scheme.is_true (Scheme.zerop __n) then
               Scheme.Num (Num.num_of_int 1)
             else
               Scheme.mul
                 (Scheme.Cons
                    {Scheme.car = __n;
                     Scheme.cdr =
                       Scheme.Cons
                         {Scheme.car =
                            Scheme.apply __fact
                              (Scheme.Cons
                                 {Scheme.car =
                                    Scheme.sub
                                      (Scheme.Cons
                                         {Scheme.car = __n;
                                          Scheme.cdr =
                                            Scheme.Cons
                                              {Scheme.car =
                                                 Scheme.Num
                                                   (Num.num_of_int 1);
                                               Scheme.cdr = Scheme.Nil}});
                                  Scheme.cdr = Scheme.Nil});
                          Scheme.cdr = Scheme.Nil}})
         | _ -> failwith "incorrect arity" ])
  in
  ignore
    (Scheme.display
       (Scheme.apply __fact
          (Scheme.Cons
             {Scheme.car = Scheme.Num (Num.num_of_int 10000);
              Scheme.cdr = Scheme.Nil})));
  Scheme.newline ()
};
