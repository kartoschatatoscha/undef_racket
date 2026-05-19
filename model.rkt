#lang racket

(require redex/reduction-semantics)
(require rackunit)


(define-language FREEZE
    ; FIGURE 4
    (stmt ::= (Name = inst) (br op Name Name) (store op op))

    (inst ::= (binop attr op op) (conv op)(bitcast op) (select op op op) (icmp cond op op) (phi ty (op label) ...) 
    (freeze op) (getelementptr op op ... op) (load op) (extractelement op const) (insertelement op op const))

    (cond ::= eq ne ugt uge slt sle)

    (ty ::= (i sz) (ptr ty) ((i sz) ...) ((ptr ty) ...))

    ;(name nat_1 natural)
    ;(name nat_2 natural)

    (binop ::= add udiv sdiv shl and or)

    (attr ::= nsw nuw exact)

    (op ::= Name const poison)

    (conv ::= zext sext trunc)

    ; NATURALS
    (nat sz const len ::= natural)
    


    ; SECTION 4.2
    ;([isz] ::= )

    ;([ptr ty]::= )

    ;([sz x ty] ::= )  TODO

    ;(Mem ::= () ...)  TODO

    ; TODO: side-condition for Name
    (Name ::= string)


    
    
    

    (Reg ::= ((Name (ty v)) ...))


    

    
)

; Num checks whether x ∈ Num(size)
; TODO: size <= 32

(define-metafunction FREEZE
    Num : sz const -> boolean  
    [(Num 0 x) (raise "bitwidth cannot be 0")]
    ;; CHECK OF WHETHER SIZE FITS WITHIN 32 BITS
    [(Num size x) (true)
     (side-condition (< (term size) 32))
     (side-condition (< (term x) (expt 2 (term size)))) ; 'x' used to be 'i' but I'm guessing that was a mistake.
     
    ]
    [(Num size x) (raise "Size cannot be larger than 32")
     (side-condition (>= (term size) 32))
    ]

    [(Num size x) (false)]
)

    ; is_Name checks whether a string refers to a variable. 
(define-metafunction FREEZE
    is_Name : string -> boolean

    [(is_Name str) true
     (side-condition (> (string-length (term str) 1)))
     (side-condition (string=? (substring (term str) 0 1) "%"))
    ]
    [(is_Name str) false]
)


(define-metafunction FREEZE
    of_ty_isz : (i sz) any -> boolean

    [(of_ty_isz (i sz) poison) true]
    [(of_ty_isz (i sz) const) (true)
     (side-condition (term (Num sz const)))
    ]

    [(of_ty_isz (i sz) x) false]
)

(define-metafunction FREEZE
    of_ty_ptr : (ptr ty) any -> boolean


    ; TODO check the validity of a type
    [(of_ty_ptr (ptr ty) poison) true]
    [(of_ty_ptr (ptr ty) const) (true)
     (side-condition (term (Num 32 const)))
    ]
    [(of_ty_ptr _ _) false]
)

(define-metafunction FREEZE
    of_ty_vec_ptr : ((ptr ty) ...) len any -> boolean

    ; TODO
    [(of_ty_vec_ptr)]
)

(define-metafunction FREEZE
    of_ty_vec_isz : ((ptr ty) ...) any -> boolean

    ; TODO
)
(define-metafunction FREEZE
    of_ty_trans : ty -> (ty -> bool)

    ;; TODO CLEANS UP THE MESS, 
)

(define-metafunction FREEZE
    of_ty : ty any -> boolean
    [(of_ty (i sz) x) (of_ty_isz x)
     ; (side-condition ,(< (term sz) 32))
    ]

    [(of_ty (ptr ty_1) x) (of_ty_ptr x)
     ; (side-condition ,(< (term sz) 32))  !!! ty_1 must actually exist
    ]

    [(of_ty ((i sz) ... ) x) (of_ty_vec_isz x)]

    [(of_ty ((ptr ty) ... ) x) (of_ty_vec_ptr x)]

)



