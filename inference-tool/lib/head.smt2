(declare-datatype Option (par (X) ((None) (Some (val X)))))
(declare-datatype Value ((Int (int Int)) (Double (double Real)) (Str (str String))))
(declare-datatype Trilean ((true) (false) (invalid)))

(define-fun Plus ((x (Option Value)) (y (Option Value))) (Option Value)
(match x (
  ((Some v1)
  (match y (
    ((Some v2)
    (match v1 (
      ((Int n1)
      (match v2 (
        ((Int n2) (Some (Int (+ n1 n2))))
        (_ None))
      ))
      ((Double n1)
      (match v2 (
        ((Double n2) (Some (Double (+ n1 n2))))
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
      ((Int n1)
      (match v2 (
        ((Int n2) (Some (Int (- n1 n2))))
        (_ None))
      ))
      ((Double n1)
      (match v2 (
        ((Double n2) (Some (Double (- n1 n2))))
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
      ((Int n1)
      (match v2 (
        ((Int n2) (Some (Int (* n1 n2))))
        (_ None))
      ))
      ((Double n1)
      (match v2 (
        ((Double n2) (Some (Double (* n1 n2))))
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
(match x (
((Some v1)
(match y (
((Some v2)
(match v1 (
  ((Int n1)
  (match v2 (
      ((Int n2) (ite (> n1 n2) true false))
      (_ invalid)
    )
  ))
  (_ invalid))
))
(_ invalid))
))
(_ invalid))
)
)

(define-fun Eq ((x (Option Value)) (y (Option Value))) Trilean
(ite (= x y) true
false)
)
