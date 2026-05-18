#lang racket

(require redex)


(define-language FREEZE
    ; FIGURE 4
    (stmt ::= (Name = inst) (br op Name Name) (store op op))

    (inst ::= (binop attr op op) (conv op)(bitcast op) (select op op op) (icmp cond op op) (phi ty (op label) ...) 
    (freeze op) (getelementptr op op ... op) (load op) (extractelement op integer) (insertelement op op integer))

    (cond ::= eq ne ugt uge slt sle)

    (ty ::= (i natural) (ptr ty) ((i natural) ...) ((ptr ty) ...))

    (binop ::= add udiv sdiv shl and or)

    (attr ::= nsw nuw exact)

    (op ::= Name integer poison)

    (conv ::= zext sext trunc)
    


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
    Num : natural natural -> boolean  
    [(Num 0 x) (raise "bitwidth cannot be 0")]
    ;; CHECK OF WHETHER SIZE FITS WITHIN 32/64 BITS
    [(Num size x) true
     (side-condition ,(< (term i) (expt 2 (term size))))
     (side-condition ,(< (term size) 32))
    ]
    [(Num size x) (raise "Size cannot be larger than 32")
     (side-condition ,(>= (term size) 32))
    ]

    [(Num size x) (false)]
)

(define-metafunction FREEZE
    is_Name : string -> boolean

    [(is_Name str) true
     (side-condition ,(> (string-length str) 1))
     (side-condition ,(string=? (substring str 0 1) "%"))
    ]
    [(is_Name str) false]
)




