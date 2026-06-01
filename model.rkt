#lang racket

(require redex)
(require rackunit)
(require rebellion/binary/bit)
(require rebellion/binary/bitstring)
(require rebellion/binary/byte)
(require helpful)


(define-language FREEZE
  
  ; FIGURE 4
  ; Building blocks
  (var ::= (% string))

  (lbl ::= string)

  (constant len index bw ::= natural) ; every use needs a check of whether it fits within 16 bits

  (tbit ::= 0 1) ; true bit

  (bit ::= tbit poisonbit)

  (byte ::= (bit bit bit bit bit bit bit bit))
  

  (bitvector ::= bit ; i1
             (bit bit ...) ; <len x i1> 
             byte ; i8
             (byte byte ...) ; <len x i8> 
             (byte byte) ; i16
             ((byte byte) (byte byte) ...)  ; <len x i16>
  )   


  ; Syntax

  (stmt ::= (var = inst)
        (store ty op (ptr ty) op)
        (br label (% lbl)) 
        (br op label (% lbl) label (% lbl))
        (label lbl)
        (ret void)
        (ret ty op)
        )

  (inst ::= (binop attr ty op op)
        (conv ty op to op)
        (bitcast ty op to ty)
        (select op ty op op)
        (icmp cond ty op op)
        (phi ty [op lbl] [op lbl] ...)
        (freeze ty op)
        (getelementptr (ptr ty) op (ty op) (ty op) ...)
        (extractelement (len x bty) op constant)
        (insertelement (len x bty) op constant)
        (load ty (ptr ty) op)
    )

  (cond ::= eq
        ne
        ugt
        uge 
        slt 
        sle)

  (sz ::= 1 8 16)

  (bty ::= (i sz))

  (ty ::= bty 
      (ptr bty)
      (len x bty)
      (ptr (len x bty)))
  
  (retty ::= ty void)

  (binop ::= add
         udiv
         sdiv
         shl
         and
         or)

  (attr ::= noattr
        nsw
        nuw
        exact)

  (op ::= var 
      constant 
      poison)

  (bval ::= constant poison)

  (vector ::= (bval ...))

  (val ::= bval vector)

  (retval ::= val void)
  
  (conv ::= zext
        sext
        trunc)
    
  (memval ::= (index byte))

  (mem ::= (memval mem) memmt)

  (regval ::= (var (ty val)))

  (reg ::= (regval reg) regmt)

  (p ::= (stmt p) mt)

  (state ::= (p reg mem lbl lbl p) UB)
  
  )


(define-metafunction FREEZE
  is_valid_ptr : index -> boolean

  [(is_valid_ptr index) #true
                        (side-condition (< (term index) (expt 2 16)))]
  [(is_valid_ptr _) #false])

    ;; Corresponds to ⟦op⟧_R in the paper

(define-metafunction FREEZE
  lookup_reg_val : reg op -> val
  
  [(lookup_reg_val _ poison) poison]

  [(lookup_reg_val _ constant) constant]

  [(lookup_reg_val regmt var) 
   (raise ,(printf "Could not find a variable ~a in the register file" (term var)))] 

  ; Found the bitvector
  [(lookup_reg_val ((var_1 (_ val_1)) reg) var_1)
   val_1]

  ; Non-empty reg, not the correct name
  [(lookup_reg_val ((var_1 (_ val_1)) reg) var_3) 
   (lookup_reg_val reg var_3)])


(define-metafunction FREEZE
  lookup_reg_ty : reg op -> ty

  [(lookup_reg_ty _ constant) (i 16)]

  [(lookup_reg_ty regmt var) 
   (raise ,(printf "Could not find a variable ~a in the register file" (term var)))] 

  ; Found the bitvector
  [(lookup_reg_ty ((var_1 (ty_1 _)) reg) var_1)
   ty_1]

  ; Name does not match, still looking through reg
  [(lookup_reg_ty ((var_1 (ty_1 _)) reg ) var_3) 
   (lookup_reg_ty reg var_3)])


(define-metafunction FREEZE
  lookup_mem : mem index -> byte
  
  [(lookup_mem _ index) (raise ,(printf "~a is not a valid pointer" (term index)))
                        (side-condition (not (term (is_valid_ptr index))))]
  [(lookup_mem memmt _) (poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit)]

  ; Found the value in memory

  [(lookup_mem ((index_1 byte_1) memmt ) index_1) byte_1] 

  ; Still looking for the value in memory

  [(lookup_mem ((index_1 byte_1) memmt ) index__3) (lookup_mem memmt index_3)])


(define-metafunction FREEZE
  type_match : reg op ty -> boolean
  [(type_match reg var ty) ,(redex-match? FREEZE ty (term (lookup_reg_ty reg var)))]
  [(type_match _ constant (i sz)) ,(< (term constant) (expt 2 (term sz)))]
  [(type_match _ constant _) #false]
  ;[(type_match _ constant ty) ,(redex-match FREEZE (i 16) (term ty))]
  
  [(type_match _ poison _) (raise "type_match error: passed poison")])

(define-metafunction FREEZE
    type_match_list : reg (op ...) ty -> boolean

    [(type_match_list _ () _) #true]

    [(type_match_list reg (op_1 op_2 ...) ty) (type_match_list reg (op_2 ...) ty)
     (side-condition (term (type_match reg op_1 ty)))
    ]

    [(type_match_list _ _ _) #false]
)

(define-metafunction FREEZE
    overflows : constant bty -> boolean

    [(overflows constant (i sz)) ,(not (< (term constant) (expt 2 (term sz))))]
)

; LOAD helpers

(define-metafunction FREEZE
    aligns : val bw -> boolean

    [(aligns index bw) ,(= 0 (modulo (term index) (term bw)))]

    [(aligns _ _) #false]
)

(define-metafunction FREEZE
    load_func : ty val mem -> val


    [(load_func (i 1) index mem) (up_ty (i 1) ,(list-ref (term (lookup_mem mem val_start)) (term val_off)))
     (where val_start ,(- (term index) (remainder (term index) 8)))
     (where val_off ,(remainder (term index) 8))
    ]

    [(load_func (i 8) index mem) (up_ty (i 8) (lookup_mem mem index))
    ]

    [(load_func (i 16) index mem) (up_ty (i 16) ((lookup_mem mem index) (lookup_mem mem index_2)))
     (where index_2 ,(+ 8 (term index)))
    ]

    [(load_func _ poison _) (raise "poison passed to load_func, not supposed to be the case!")]

    [(load_func _ vector _) (raise "vector passed to load_func, not supposed to be the case!")]

    ; TODO Load for vectors

)

(define-metafunction FREEZE
    store_func : ty val val mem -> mem ; First is the value to be stored, then the index

    [(store_func _ _ poison _) (raise "poison pointer passed to store_func, not supposed to be the case!")]

    [(store_func _ _ vector _) (raise "vector pointer passed to store_func, not supposed to be the case!")]

    [(store_func (i 1) constant index mem) ((index_start ,(list-set (term byte) (term index_off) (term (down_ty (i 1) constant)))) mem)
     (where byte (lookup_mem mem ,(- (term index) (remainder (term index) 8))))
     (where index_off ,(remainder (term index) 8))
     (where index_start ,(- (term index) (remainder (term index) 8)))
    ]
    [(store_func (i 8) constant index mem) ((index (down_ty (i 8) constant)) mem)]

    [(store_func (i 16) constant index mem) ((index_2 (down_ty (i 8) constant_2)) ((index (down_ty (i 8) constant_1)) mem)) 
    (where constant_1 ,(bitwise-and (term constant) 255))
    (where constant_2 ,(arithmetic-shift (term constant) -8))
    (where index_2 ,(+ 8 (term index)))
    ]

    ; TODO vectors


)

(define-metafunction FREEZE
    bitwidth : ty -> bw

    [(bitwidth (i sz)) sz]

    [(bitwidth (ptr _)) 16]

    [(bitwidth _) (raise "case of bitwidth not implemented")]
)

(define-metafunction FREEZE
    has_poison : bitvector -> boolean
    ; function only to be invoked for i1, i8, and i16!

    [(has_poison poisonbit) #true]

    [(has_poison (bit ... poisonbit bit ...)) #true]

    [(has_poison (byte_1 byte_2)) #true
     (side-condition (or (term (has_poison byte_1)) (term (has_poison byte_2))))
    ]

    [(has_poison _) #false]
)

(define-metafunction FREEZE
    down_ty : ty val -> bitvector

    [(down_ty (i sz) val) (down_ty_isz (i sz) val)]

    [(down_ty (ptr _) val) (down_ty_isz (i 16) val)]

    ;; TODO for vectors
)
(define-metafunction FREEZE
    up_ty : ty bitvector -> val

    [(up_ty (i sz) bitvector) (up_ty_isz (i sz) bitvector)]

    [(up_ty (ptr _) bitvector) (up_ty_isz (i 16) bitvector)]

    ;; TODO for vectors
)

(define-metafunction FREEZE
    up_ty_isz : ty bitvector -> val

    [(up_ty_isz _ bitvector) poison
     (side-condition (term (has_poison bitvector)))
    ]
    
    [(up_ty_isz (i 1) tbit) tbit]

    [(up_ty_isz (i 8) byte_1) ,(apply byte (term byte_1))]

    [(up_ty_isz (i 16) (byte_1 byte_2)) ,(+ (* 256 (apply byte (term byte_1))) (apply byte (term byte_2)))]

)

(define-metafunction FREEZE
    down_ty_isz : (i sz) val -> bitvector

    ;MAYBETODO one can clean up the function by having poison bytes, but that would require to adjust the memory modification function
    [(down_ty_isz (i 1) poison) poisonbit]

    [(down_ty_isz (i 1) constant) constant]

    [(down_ty_isz (i 8) poison) 
    (to_byte poison)]

    [(down_ty_isz (i 8) constant) (to_byte constant)]
    
    [(down_ty_isz (i 16) poison) ((to_byte poison) (to_byte poison))
    ]

    [(down_ty_isz (i 16) constant) ((to_byte constant) (to_byte constant_2))
     (where constant_2 ,(quotient (term constant) 256))
    ]
)


(define-metafunction FREEZE
    to_byte_helper : constant (bit ...) index -> (bit ...)

    [(to_byte_helper _ (bit ...) 0) (bit ...)]

    [(to_byte_helper constant (bit ...) index) 
     (to_byte_helper constant_2 (,(modulo (term constant) 2) bit ...) index_2)

     (where constant_2 ,(quotient (term constant) 2))
     (where index_2 ,(- (term index) 1))
     (side-condition (and (> (term index) 0) (< (term index) 9)))
    ]

    [(to_byte_helper  _ _ _) (raise "to_byte_helper not called with a valid domain")]

)
(define-metafunction FREEZE
    to_byte : val -> byte

    [(to_byte vector) (raise "to_byte with vector must not be called!")]

    [(to_byte poison) (poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit)]

    [(to_byte constant) 
     (to_byte_helper constant () 8)  ; a is the list element, (b c) is the current constant with the byte string
    ]
)
(define-metafunction FREEZE
    find_lbl : p lbl -> p

    [(find_lbl mt lbl) (raise ,(printf "~a not found" (term lbl)))]

    [(find_lbl ((label lbl) p) lbl) p]

    [(find_lbl (stmt p) lbl) (find_lbl p lbl)]

)
(define-metafunction FREEZE
    start : p -> state ;; start with entry

    [(start p) (p_entry regmt memmt "entry" "" p) ; entry is the current, "" is the previous
     (where p_entry (find_lbl p "entry"))
    ]    ;; Memory uninitialized
)

(define-metafunction FREEZE
    end : state -> (retty retval) or UB

    [(end UB) UB]

    [(end (mt (((% "retval") (ty val)) reg) _ _ _ _))
     (ty val)
    ] ; retval is present
    [(end (mt ((var (ty val)) reg) mem lbl_1 lbl_2 p))
     (end (mt reg mem lbl_1 lbl_2 p))
    ]

    [(end (mt regmt _ _ _ _)) (void void)]
)





(define -->R 
    (reduction-relation FREEZE
    
    ;; Rules in the paper

    ; freeze isz

    [--> (((var = (freeze (i sz) op)) p_rest) reg mem lbl_1 lbl_2 p)
     (p_rest ((var ((i sz) ,(random (expt 2 (term sz))))) reg) mem lbl_1 lbl_2 p)
     (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op))))
    fr_poison]

    [--> (((var = (freeze (i sz) op)) p_rest) reg mem lbl_1 lbl_2 p)
     (p_rest ((var ((i sz) (lookup_reg_val reg var))) reg) mem lbl_1 lbl_2 p)
     (side-condition (not(redex-match? FREEZE poison (term (lookup_reg_val reg op)))))
     (side-condition (redex-match? FREEZE (term (i sz)) (term (lookup_reg_ty reg op))))
    fr]    

    ;; TODO freeze for vectors


    [--> (((var = (phi ty [op_1 lbl_1] ... [op lbl_prev] [op_2 lbl_2] ...)) p_rest) reg mem lbl_curr lbl_prev p)
     (p_rest ((var (ty val)) reg) mem lbl_curr lbl_prev p)
     (where val (lookup_reg_val reg op))
     (side-condition (term (type_match reg op ty))) ; TODO all variables have to be checked
    phi]

    [--> (((var = (select op_c ty op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p)
     (p_rest ((var (ty poison)) reg) mem lbl_1 lbl_2 p)
     (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op_c))))
     (side-condition (term (type_match reg op_1 ty)))
     (side-condition (term (type_match reg op_2 ty)))
    sel_poison]

    [--> (((var = (select op_c ty op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p)
     (p_rest ((var (ty val_1)) reg) mem lbl_1 lbl_2 p)
     
     (where val_1 (lookup_reg_val reg op_1))
     (where val_c (lookup_reg_val reg op_c)) ;; TODO

     (side-condition (redex-match? FREEZE (term 1) (term (lookup_reg_val reg op_c))))
     (side-condition (term (type_match reg op_1 ty)))
     (side-condition (term (type_match reg op_2 ty)))
     
    sel_1]

    [--> (((var = (select op_c ty op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p)
     (p_rest ((var (ty val_2)) reg) mem lbl_1 lbl_2 p)

     (where val_2 (lookup_reg_val reg op_2))

     (side-condition (redex-match? FREEZE (term 0) (term (lookup_reg_val reg op_c))))
     (side-condition (term (type_match reg op_1 ty)))
     (side-condition (term (type_match reg op_2 ty)))
     
    sel_2]


    [--> (((var = (and noattr (i sz) op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p)
    (p_rest ((var ((i sz) poison)) reg) mem lbl_1 lbl_2 p)

    (side-condition 
        (or 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    
    and_poison]
    ; LLVM's and on integers is bitwise-and
    [--> (((var = (and noattr (i sz) op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p)
    (p_rest ((var ((i sz) ,(bitwise-and (term val_1) (term val_2)))) reg) mem lbl_1 lbl_2 p)

    (where val_1 (lookup_reg_val reg op_1))
    (where val_2 (lookup_reg_val reg op_2))

    (side-condition 
        (nor 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    
    and]

    [--> (((var = (add nuw (i sz) op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p)
    (p_rest ((var ((i sz) poison)) reg) mem lbl_1 lbl_2 p)

    (side-condition 
        (or 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    
    add_nuw_poison]

    [--> (((var = (add nuw (i sz) op_1 op_2)) p_rest ) reg mem lbl_1 lbl_2 p)
    (p_rest ((var ((i sz) ,(+ (term val_1) (term val_2)))) reg) mem lbl_1 lbl_2 p)

    (where val_1 (lookup_reg_val reg op_1))
    (where val_2 (lookup_reg_val reg op_2))

    (side-condition 
        (nor 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (not (term (overflows ,(+ (term (lookup_reg_val reg op_1)) (term (lookup_reg_val reg op_2))) (i sz)))))
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    add_nuw]

    [--> (((var = (add nuw (i sz) op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p)
    (p_rest ((var ((i sz) poison)) reg) mem lbl_1 lbl_2 p)
    (side-condition 
        (nor 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (term (overflows ,(+ (term (lookup_reg_val reg op_1)) (term (lookup_reg_val reg op_2))) (i sz))))
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))

    add_nuw_over] ;; Overflow with nuw returns poison

    [--> (((var = (bitcast ty_1 op to ty_2)) p_rest) reg mem lbl_1 lbl_2 p)
    (p_rest ((var (ty_2 (up_ty ty_2 (down_ty ty_1 val)))) reg) mem lbl_1 lbl_2 p)

    (where val (lookup_reg_val reg op))

    (side-condition (term (type_match reg op ty_1)))
    bitcast]

    ;; TODO load 

    [--> (((var = (load ty (ptr ty) op)) p_rest) reg mem lbl_1 lbl_2 p) ;(load ty (ptr ty) op)
         (p_rest ((var (ty (load_func ty (lookup_reg_val reg op) mem))) reg) mem lbl_1 lbl_2 p)

         (side-condition (term (type_match reg op (ptr ty))))
         (side-condition (term (aligns (lookup_reg_val reg op) (bitwidth ty)))) ; aligns is different for vectors, has to be only base types
         (side-condition (not (redex-match? FREEZE poison (term (lookup_reg_val reg op)))))
         (side-condition (not (redex-match? FREEZE poison (term (load_func ty (lookup_reg_val reg op) mem)))))

    load]

    [--> (((var = (load ty (ptr ty) op)) p_rest) reg mem lbl_1 lbl_2 p) ;(load ty (ptr ty) op)
         (p_rest ((var (ty (load_func ty (lookup_reg_val reg op) mem))) reg) mem lbl_1 lbl_2 p)

         (side-condition (term (type_match reg op (ptr ty))))
         (side-condition (term (aligns (lookup_reg_val reg op) (bitwidth ty))))
         (side-condition (not (redex-match? FREEZE poison (term (lookup_reg_val reg op)))))
         (side-condition (redex-match? FREEZE poison (term (load_func ty (lookup_reg_val reg op) mem))))

    load_poison_val]

    [--> (((var = (load ty (ptr ty) op)) p_rest) reg mem lbl_1 lbl_2 p) ;(load ty (ptr ty) op)
         UB

         (side-condition (term (type_match reg op (ptr ty))))
         (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op))))
    load_poison_ptr]        

    ;; TODO store
    [--> (((store bty op_1 (ptr bty) op_2) p_rest) reg mem lbl_1 lbl_2 p)
         (p_rest reg (store_func bty (lookup_reg_val reg op_1) (lookup_reg_val reg op_2) mem) lbl_1 lbl_2 p)

         ;(side-condition (and (term (type_match reg op_1 bty)) (term (type_match reg op_2 (ptr bty)))))
         (side-condition (term (aligns (lookup_reg_val reg op_2) (bitwidth bty))))

    store]

    [--> (((store ty op_1 (ptr ty) op_2) p_rest) reg mem lbl_1 lbl_2 p) ;(load ty (ptr ty) op)
         UB

         (side-condition (term (type_match reg op_2 (ptr ty))))
         (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op_2))))
    store_poison_ptr]  ; (store ty op (ptr ty) op)

    ;; Return
    [--> (((ret void) p_rest) reg mem lbl_1 lbl_2 p)
         (mt reg mem lbl_1 lbl_2 p)  ; If there is no retval then the return type is void
    ret_void]

    [--> (((ret ty op) p_1) reg mem lbl_1 lbl_2 p)
         (mt (((% "retval") (ty val)) reg) mem lbl_1 lbl_2 p)
         (where val (lookup_reg_val reg op))
         (side-condition (term (type_match reg op ty)))
    ret_ty]
    ;; Branching (br label (% lbl)) 
    [--> (((br label (% lbl_br)) p_rest) reg mem lbl_curr lbl_prev p)
         (p_lbl reg mem lbl_br lbl_curr p)
         (where p_lbl (find_lbl p lbl_br))
    br_lbl]

    
    [--> (((br op label (% lbl_1) label (% lbl_2)) p_rest) reg mem lbl_curr _ p)
         (p_1 reg mem lbl_1 lbl_curr p)
         (where p_1 (find_lbl p lbl_1))
         
         (side-condition (and (not (redex-match? FREEZE poison (term (lookup_reg_val reg op)))) (not (zero? (term (lookup_reg_val reg op))))))
         (side-condition (term (type_match reg op (i 1))))
    br_1]

    [--> (((br op label (% lbl_1) label (% lbl_2)) p_rest) reg mem lbl_curr lbl_prev p)
         (p_2 reg mem lbl_2 lbl_curr p)
         (where p_2 (find_lbl p lbl_2))
         (side-condition (and (not (redex-match? FREEZE poison (term (lookup_reg_val reg op)))) (zero? (term (lookup_reg_val reg op)))))
         (side-condition (term (type_match reg op (i 1))))
    br_2]

    [--> (((br op label (% lbl_1) label (% lbl_2)) p_rest) reg mem lbl_curr lbl_prev p)
         UB ; TODO
         (where p_2 (find_lbl p lbl_2)); TODO
         (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op))))
    br_poison] 

    [--> (((label lbl) p_rest) reg mem lbl_curr _ p)
         (p_rest reg mem lbl lbl_curr p)
    lbl]
    ;; Additional rules
    )

)

(define-metafunction FREEZE
    make_program : (stmt ...) -> p

    [(make_program ()) mt]

    [(make_program (stmt_1 stmt_2 ...)) (stmt_1 (make_program (stmt_2 ...)))]
)

;(redex-match? FREEZE state (term (((label "entry")
;(((% "trig") = (load (i 16) (ptr (i 16)) (% "p_ptr") )) mt)) (((% "p_ptr") ((ptr (i 16)) poison)) regmt) memmt "" "" mt) ))
;(traces -->R (term (start ((label "entry") (((% "val") = (add nuw (i 16) 65535 1)) ((ret (i 16) (% "val")) ((ret (i 16) (% "val")) mt)))))))
;(term (end ,(first (apply-reduction-relation* -->R (term (((label "entry") (((% "trig") = (load (i 16) (ptr (i 16)) (% "p_ptr") )) mt)) (((% "p_ptr") ((ptr (i 16)) poison)) regmt) memmt "" "" mt))))))
;(traces -->R (term (((store (i 16) 257 (ptr (i 16)) 0) mt) regmt memmt "" "" mt) ) )
;(redex-match? FREEZE stmt (term (br (% "c2") label (% "then") label (% "else"))))
(define-term l_unsw_before
    (make_program 
(
    (label "entry")
    ((% "c") = (add nuw (i 1) 0 0))
    ((% "c2") = (add nuw (i 1) 1 1))
    (br (% "c") label (% "while") label (% "end"))

    (label "while")
    (br (% "c2") label (% "then") label (% "else"))

    (label "then")
    (ret (i 16) 2)

    (label "else")
    (ret (i 16) 1)

    (label "end")
    (ret (i 16) 0)
)
)
)


(define-term l_unsw_after(
    make_program (
    (label "entry")
    ((% "c") = (add nuw (i 1) 0 0))
    ((% "c2") = (add nuw (i 1) 1 1))
    ((% "c_fr") = (freeze (i 1) (% "c2")))
    (br label (% "if"))

    (label "if")
    (br (% "c_fr") label (% "then") label (% "else"))

    (label "then")
    (br (% "c") label (% "while_then") label (% "end"))

    (label "else")
    (br (% "c") label (% "while_else") label (% "end"))

    (label "while_then")
    (ret (i 16) 2)

    (label "while_else")
    (ret (i 16) 1)

    (label "end")
    (ret (i 16) 0)
    )

)
)

(define-term rev_pred_before(
    make_program (
        (label "entry")
        ((% "c") = (add nuw (i 1) 1 1))
        ((% "x") = (select (% "c") (i 16) 100 10))
        (ret (i 16) (% "x"))
    )

)

)  
(define-term rev_pred_after (
    make_program (
        (label "entry")
        ((% "c") = (add nuw (i 1) 1 1))
        ((% "c2") = (freeze (i 1) (% "c")))
        (br (% "c2") label (% "true") label (% "false"))

        (label "true")
        (br label (% "merge"))

        (label "false")
        (br label (% "merge"))

        (label "merge")
        ((% "x") = (phi (i 16) [100 "true"] [10 "false"]))
        (ret (i 16) (% "x"))
    )
)

)
;(traces -->R (term (start rev_pred_after)))

(term (end ,(first (apply-reduction-relation* -->R (term (start rev_pred_after))))))
(term (end ,(first (apply-reduction-relation* -->R (term (start rev_pred_after))))))

(term (end ,(first (apply-reduction-relation* -->R (term (start rev_pred_after))))))

(term (end ,(first (apply-reduction-relation* -->R (term (start rev_pred_after))))))

(term (end ,(first (apply-reduction-relation* -->R (term (start rev_pred_after))))))


