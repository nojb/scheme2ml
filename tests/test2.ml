do {
  ignore
    (Scheme.display
       (Scheme.add
          (Scheme.Cons
             {Scheme.car = Scheme_read.read ();
              Scheme.cdr =
                Scheme.Cons
                  {Scheme.car = Scheme.Num (Num.num_of_int 1);
                   Scheme.cdr = Scheme.Nil}})));
  Scheme.newline ()
};
