(declare-datatype Option (par (X) ((None) (Some (val X)))))
(declare-datatype Value ((Num (num Int)) (Str (str String))))
(declare-datatype Trilean ((true) (false) (invalid)))

(define-fun Plus ((x (Option Value)) (y (Option Value))) (Option Value)
(match x (
  ((Some v1)
  (match y (
    ((Some v2)
    (match v1 (
      ((Num n1)
      (match v2 (
        ((Num n2) (Some (Num (+ n1 n2))))
        (_ None))
      ))
      (_ None))
    ))
    (_ None))
  ))
  (_ None))
)
)

(define-fun Minus ((x (Option Value)) (y (Option Value))) (Option Value)
(match x (
((Some v1)
(match y (
  ((Some v2)
  (match v1 (
    ((Num n1)
    (match v2 (
      ((Num n2) (Some (Num (- n1 n2))))
      (_ None))
    ))
    (_ None))
  ))
  (_ None))
))
(_ None))
)
)

(define-fun Times ((x (Option Value)) (y (Option Value))) (Option Value)
(match x (
((Some v1)
(match y (
((Some v2)
(match v1 (
  ((Num n1)
  (match v2 (
    ((Num n2) (Some (Num (* n1 n2))))
    (_ None))
  ))
  (_ None))
))
(_ None))
))
(_ None))
)
)

(define-fun Nor ((x Trilean) (y Trilean)) Trilean
(ite (and (= x true) (= y true)) false
(ite (and (= x true) (= y false)) false
(ite (and (= x false) (= y true)) false
(ite (and (= x false) (= y false)) true
invalid))))
)

(define-fun Or ((x Trilean) (y Trilean)) Trilean
(ite (and (= x true) (= y true)) true
(ite (and (= x true) (= y false)) true
(ite (and (= x false) (= y true)) true
(ite (and (= x false) (= y false)) false
invalid))))
)

(define-fun Gt ((x (Option Value)) (y (Option Value))) Trilean
(ite (exists ((x1 Int)) (exists ((y1 Int)) (and (= x (Some (Num x1))) (and (= y (Some (Num y1))) (> x1 y1))))) true
(ite (exists ((x1 Int)) (exists ((y1 Int)) (and (= x (Some (Num x1))) (and (= y (Some (Num y1))) (not (> x1 y1)))))) false
invalid))
)

(define-fun Eq ((x (Option Value)) (y (Option Value))) Trilean
(ite (= x y) true
false)
)
