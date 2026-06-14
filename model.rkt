#lang racket

(require redex)
(require rackunit)
(require rebellion/binary/bit)
(require rebellion/binary/bitstring)
(require rebellion/binary/byte)
(require helpful)
(require racket/match)


(define-language FREEZE
  
  ; Syntax
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

  (nonderef ::= (var ...))

  (p ::= (stmt p) mt)

  (state ::= (p reg mem lbl lbl p nonderef) UB)
  
  )


(define-metafunction FREEZE
  is_valid_ptr : index -> boolean

  [(is_valid_ptr 0) #false]

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

  [(lookup_reg_ty _ constant) (raise "constant type depends on the context!")]

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

  [(lookup_mem ((index_1 byte_1) memmt ) index_3) (lookup_mem memmt index_3)])


(define-metafunction FREEZE
  type_match : reg op ty -> boolean
  [(type_match reg var ty_1) ,(redex-match? FREEZE ty_1 (term (lookup_reg_ty reg var)))]
  [(type_match _ constant (i sz)) ,(< (term constant) (expt 2 (term sz)))]
  [(type_match _ constant _) #false]
  ;[(type_match _ constant ty) ,(redex-match FREEZE (i 16) (term ty))]
  
  [(type_match _ poison _) #true]
)

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

    [(load_func (len x bty) index mem)
    ()
    (side-condition (= 0 (term len)))
    ]

    [(load_func (len_1 x bty) index mem) ,(append (term ((load_func bty index mem))) (term (load_func (len_2 x bty) index_2 mem)))

    ;(where val_load (load_func bty index mem))
    (where index_2 ,(+ (term (bitwidth bty)) (term index)))
    (where len_2 ,(- (term len_1) 1))
    (side-condition (> (term len_1) 0))

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

    [(store_func (i 1) poison index mem) ((index_start ,(list-set (term byte) (term index_off) (term (down_ty (i 1) poison)))) mem)
     (where byte (lookup_mem mem ,(- (term index) (remainder (term index) 8))))
     (where index_off ,(remainder (term index) 8))
     (where index_start ,(- (term index) (remainder (term index) 8)))
    ]
    [(store_func (i 8) constant index mem) ((index (down_ty (i 8) constant)) mem)]
    [(store_func (i 8) poison index mem) ((index (down_ty (i 8) poison)) mem)]

    [(store_func (i 16) constant index mem) ((index_2 (down_ty (i 8) constant_2)) ((index (down_ty (i 8) constant_1)) mem)) 
    (where constant_1 ,(bitwise-and (term constant) 255))
    (where constant_2 ,(arithmetic-shift (term constant) -8))
    (where index_2 ,(+ 8 (term index)))
    ]

    [(store_func (i 16) poison index mem) ((index_2 (down_ty (i 8) poison)) ((index (down_ty (i 8) poison)) mem)) 
     (where index_2 ,(+ 8 (term index)))
    ]

    ; TODO vectors

    [(store_func (0 x bty) () index mem) mem]

    [(store_func (len_1 x bty) (val_1 val_2 ...) index_1 mem_1)
     (store_func (len_2 x bty) (val_2 ...) index_2 mem_2)

     (side-condition (> (term len_1) 0))
     (where len_2 ,(- (term len_1) 1))
     (where index_2 ,(+ (term index_1) (term (bitwidth bty))))
     (where mem_2 (store_func bty val_1 index_1 mem_1))

    ]


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

    [(has_poison (bit_1 ... poisonbit bit_2 ...)) #true]

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
    piecewise_freeze : bty (bval ...) -> (bval ...)
    [(piecewise_freeze (i sz) ()) ()]

    [(piecewise_freeze (i sz) (constant bval ...)) ,(append (term (constant)) (term (piecewise_freeze (i sz) (bval ...))))]

    [(piecewise_freeze (i sz) (poison bval ...)) ,(append (term (,(random (expt 2 (term sz))))) (term (piecewise_freeze (i sz) (bval ...))))]

)


(define-metafunction FREEZE
    start : p -> state ;; start with entry

    [(start p) (p_entry regmt memmt "entry" "" p ()) ; entry is the current, "" is the previous
     (where p_entry (find_lbl p "entry"))
    ]    ;; Memory uninitialized
)

(define-metafunction FREEZE
    end : state -> (retty retval) or UB

    [(end UB) UB]

    [(end (mt (((% "retval") (ty val)) reg) _ _ _ _ _))
     (ty val)
    ] ; retval is present
    [(end (mt ((var (ty val)) reg) mem lbl_1 lbl_2 p nonderef))
     (end (mt reg mem lbl_1 lbl_2 p nonderef))
    ]

    [(end (mt regmt _ _ _ _ _)) (void void)]
)





(define -->R 
    (reduction-relation FREEZE
    
    ;; Rules in the paper

    ; freeze isz

    [--> (((var = (freeze (i sz) op)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
     (p_rest ((var ((i sz) ,(random (expt 2 (term sz))))) reg) mem lbl_1 lbl_2 p nonderef)
     (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op))))
     (side-condition (term (type_match reg op (i sz))))
    fr_poison]

    [--> (((var = (freeze ty_op op)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
     (p_rest ((var (ty_op (lookup_reg_val reg op))) reg) mem lbl_1 lbl_2 p nonderef)
     (side-condition (not(redex-match? FREEZE poison (term (lookup_reg_val reg op)))))
     (side-condition (term (type_match reg op ty_op)))
    fr_val]  

    ;TODO freeze for pointers

    [--> (((var = (freeze (ptr ty) op)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
        (p_rest ((var ((ptr ty) ,(random (expt 2 16)))) reg) mem lbl_1 lbl_2 p nonderef_2)

        (where nonderef_2 ,(append (term (var)) (term nonderef)))
        (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op))))
        (side-condition (term (type_match reg op (ptr ty))))
    
    fr_ptr]  

    ;; TODO freeze for vectors
    [--> (((var = (freeze (len x bty) op)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
    (p_rest ((var ((len x bty) (piecewise_freeze bty vector))) reg) mem lbl_1 lbl_2 p nonderef)
    (side-condition (term (type_match reg op (len x bty))))
    (where vector (lookup_reg_val reg op))
    fr_vector]

    [--> (((var = (phi ty [op_1 lbl_1] ... [op lbl_prev] [op_2 lbl_2] ...)) p_rest) reg mem lbl_curr lbl_prev p nonderef)
     (p_rest ((var (ty val)) reg) mem lbl_curr lbl_prev p nonderef)
     (where val (lookup_reg_val reg op))
     (side-condition (term (type_match reg op ty))) ; TODO all variables have to be checked
    phi]

    [--> (((var = (select op_c ty op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
     (p_rest ((var (ty poison)) reg) mem lbl_1 lbl_2 p nonderef)
     (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op_c))))
     (side-condition (term (type_match reg op_1 ty)))
     (side-condition (term (type_match reg op_2 ty)))
    sel_poison]

    [--> (((var = (select op_c ty op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
     (p_rest ((var (ty val_1)) reg) mem lbl_1 lbl_2 p nonderef)
     
     (where val_1 (lookup_reg_val reg op_1))
     (where val_c (lookup_reg_val reg op_c)) ;; TODO

     (side-condition (redex-match? FREEZE 1 (term (lookup_reg_val reg op_c))))
     (side-condition (term (type_match reg op_1 ty)))
     (side-condition (term (type_match reg op_2 ty)))
     
    sel_1]

    [--> (((var = (select op_c ty op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
     (p_rest ((var (ty val_2)) reg) mem lbl_1 lbl_2 p nonderef)

     (where val_2 (lookup_reg_val reg op_2))

     (side-condition (redex-match? FREEZE 0 (term (lookup_reg_val reg op_c))))
     (side-condition (term (type_match reg op_1 ty)))
     (side-condition (term (type_match reg op_2 ty)))
     
    sel_2]

    [--> (((var = (extractelement (len x bty) op constant)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
        (p_rest ((var (bty val)) reg) mem lbl_1 lbl_2 p nonderef)

        (side-condition (term (type_match reg op (len x bty))))
        (where val ,(list-ref (term (lookup_reg_val reg op)) (term constant)))
    
    extr]


    [--> (((var = (and noattr (i sz) op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
    (p_rest ((var ((i sz) poison)) reg) mem lbl_1 lbl_2 p nonderef)

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
    [--> (((var = (and noattr (i sz) op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
    (p_rest ((var ((i sz) ,(bitwise-and (term val_1) (term val_2)))) reg) mem lbl_1 lbl_2 p nonderef)

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

    [--> (((var = (add nuw (i sz) op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
    (p_rest ((var ((i sz) poison)) reg) mem lbl_1 lbl_2 p nonderef)

    (side-condition 
        (or 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    
    add_nuw_poison]

    [--> (((var = (add nuw (i sz) op_1 op_2)) p_rest ) reg mem lbl_1 lbl_2 p nonderef)
    (p_rest ((var ((i sz) ,(+ (term val_1) (term val_2)))) reg) mem lbl_1 lbl_2 p nonderef)

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

    [--> (((var = (add nuw (i sz) op_1 op_2)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
    (p_rest ((var ((i sz) poison)) reg) mem lbl_1 lbl_2 p nonderef)
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

    [--> (((var = (bitcast ty_1 op to ty_2)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
    (p_rest ((var (ty_2 (up_ty ty_2 (down_ty ty_1 val)))) reg) mem lbl_1 lbl_2 p nonderef)

    (where val (lookup_reg_val reg op))

    (side-condition (term (type_match reg op ty_1)))
    bitcast]

    ;; TODO load 

    [--> (((var = (load ty (ptr ty) op)) p_rest) reg mem lbl_1 lbl_2 p nonderef) ;(load ty (ptr ty) op)
         (p_rest ((var (ty (load_func ty (lookup_reg_val reg op) mem))) reg) mem lbl_1 lbl_2 p nonderef)

         (side-condition (term (type_match reg op (ptr ty))))
         (side-condition (redex-match? FREEZE bty (term ty)))
         (side-condition (term (aligns (lookup_reg_val reg op) (bitwidth ty)))) ; aligns is different for vectors, has to be only base types
         (side-condition (not (redex-match? FREEZE poison (term (lookup_reg_val reg op)))))
         (side-condition (not (redex-match? FREEZE poison (term (load_func ty (lookup_reg_val reg op) mem)))))
         (side-condition (false? (member (term op) (term nonderef))))

    load_isz]

    [--> (((var = (load (len x bty) (ptr (len x bty)) op)) p_rest) reg mem lbl_1 lbl_2 p nonderef) ;(load ty (ptr ty) op)
         (p_rest ((var ((len x bty) (load_func (len x bty) (lookup_reg_val reg op) mem))) reg) mem lbl_1 lbl_2 p nonderef)

         (side-condition (term (type_match reg op (ptr (len x bty)))))
         (side-condition (term (aligns (lookup_reg_val reg op) (bitwidth bty)))) ; aligns is different for vectors, has to be only base types
         ; TODO there has to be enough memory
         (side-condition (not (redex-match? FREEZE poison (term (lookup_reg_val reg op)))))
         (side-condition (not (redex-match? FREEZE poison (term (load_func (len x bty) (lookup_reg_val reg op) mem)))))
         (side-condition (false? (member (term op) (term nonderef))))

    load_vector]

    [--> (((var = (load ty (ptr ty) op)) p_rest) reg mem lbl_1 lbl_2 p nonderef) ;(load ty (ptr ty) op)
         (p_rest ((var (ty (load_func ty (lookup_reg_val reg op) mem))) reg) mem lbl_1 lbl_2 p nonderef)

         (side-condition (term (type_match reg op (ptr ty))))
         (side-condition (not (redex-match? FREEZE (len x bty) (term ty))))
         (side-condition (term (aligns (lookup_reg_val reg op) (bitwidth ty))))
         (side-condition (not (redex-match? FREEZE poison (term (lookup_reg_val reg op)))))
         (side-condition (redex-match? FREEZE poison (term (load_func ty (lookup_reg_val reg op) mem))))
         (side-condition (false? (member (term op) (term nonderef))))

    load_poison_val]

    [--> (((var = (load ty (ptr ty) op)) p_rest) reg mem lbl_1 lbl_2 p nonderef) ;(load ty (ptr ty) op)
         UB

         (side-condition (term (type_match reg op (ptr ty))))
         (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op))))
    load_poison_ptr]   

    [--> (((var = (load ty (ptr ty) op)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
        UB
        (side-condition (term (type_match reg op (ptr ty))))
        (side-condition (false? (false? (member (term op) (term nonderef)))))
        
    load_nonderef]
    ;[--> (((var = (load ty (ptr ty) op)) p_rest) reg mem lbl_1 lbl_2 p nonderef)
       ;UB
      ;(side-condition (term (type_match reg op (ptr ty))))
     ; (side-condition (not (term (aligns (lookup_reg_val reg op) (bitwidth ty)))))
        
    ;load_misaligned] 

    ;; TODO store
    [--> (((store bty op_1 (ptr bty) op_2) p_rest) reg mem lbl_1 lbl_2 p nonderef)
         (p_rest reg (store_func bty (lookup_reg_val reg op_1) (lookup_reg_val reg op_2) mem) lbl_1 lbl_2 p nonderef)

         (side-condition (and (term (type_match reg op_1 bty)) (term (type_match reg op_2 (ptr bty)))))
         (side-condition (term (aligns (lookup_reg_val reg op_2) (bitwidth bty))))
         (side-condition (not (redex-match? FREEZE poison (term (lookup_reg_val reg op_2)))))

    store]

    [--> (((store (len x bty) op_1 (ptr (len x bty)) op_2) p_rest) reg mem lbl_1 lbl_2 p nonderef)
         (p_rest reg (store_func (len x bty) (lookup_reg_val reg op_1) (lookup_reg_val reg op_2) mem) lbl_1 lbl_2 p nonderef)

         (side-condition (false? (member (term op_2) (term nonderef))))
         (side-condition (not (redex-match? FREEZE poison (term (lookup_reg_val reg op_2)))))
    
    store_vec_val]

    [--> (((store ty op_1 (ptr ty) op_2) p_rest) reg mem lbl_1 lbl_2 p nonderef) ;(load ty (ptr ty) op)
         UB

         (side-condition (term (type_match reg op_2 (ptr ty))))
         (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op_2))))
    store_poison_ptr]  ; (store ty op (ptr ty) op)
    [--> (((store ty op_1 (ptr ty) op_2) p_rest) reg mem lbl_1 lbl_2 p nonderef) ;(load ty (ptr ty) op)
         UB

         (side-condition (term (type_match reg op_2 (ptr ty))))
         (side-condition (false? (false? (member (term op_2) (term nonderef)))))
         
    store_nonderef_ptr]  ; (store ty op (ptr ty) op)

    ;; Return
    [--> (((ret void) p_rest) reg mem lbl_1 lbl_2 p nonderef)
         (mt reg mem lbl_1 lbl_2 p nonderef)  ; If there is no retval then the return type is void
    ret_void]

    [--> (((ret ty op) p_1) reg mem lbl_1 lbl_2 p nonderef)
         (mt (((% "retval") (ty val_1)) reg) mem lbl_1 lbl_2 p nonderef)
         (where val_1 (lookup_reg_val reg op))
         (side-condition (term (type_match reg op ty)))
    ret_ty]
    ;; Branching (br label (% lbl)) 
    [--> (((br label (% lbl_br)) p_rest) reg mem lbl_curr lbl_prev p nonderef)
         (p_lbl reg mem lbl_br lbl_curr p nonderef)
         (where p_lbl (find_lbl p lbl_br))
    br_lbl]

    
    [--> (((br op label (% lbl_1) label (% lbl_2)) p_rest) reg mem lbl_curr _ p nonderef)
         (p_1 reg mem lbl_1 lbl_curr p nonderef)
         (where p_1 (find_lbl p lbl_1))
         
         (side-condition (and (not (redex-match? FREEZE poison (term (lookup_reg_val reg op)))) (not (zero? (term (lookup_reg_val reg op))))))
         (side-condition (term (type_match reg op (i 1))))
    br_1]

    [--> (((br op label (% lbl_1) label (% lbl_2)) p_rest) reg mem lbl_curr lbl_prev p nonderef)
         (p_2 reg mem lbl_2 lbl_curr p nonderef)
         (where p_2 (find_lbl p lbl_2))
         (side-condition (and (not (redex-match? FREEZE poison (term (lookup_reg_val reg op)))) (zero? (term (lookup_reg_val reg op)))))
         (side-condition (term (type_match reg op (i 1))))
    br_2]

    [--> (((br op label (% lbl_1) label (% lbl_2)) p_rest) reg mem lbl_curr lbl_prev p nonderef)
         UB 
         (where p_2 (find_lbl p lbl_2)); TODO
         (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op))))
    br_poison] 

    [--> (((label lbl) p_rest) reg mem lbl_curr _ p nonderef)
         (p_rest reg mem lbl lbl_curr p nonderef)
    lbl]
    ;; Additional rules
    )

)

(define-metafunction FREEZE
    make_program : (stmt ...) -> p

    [(make_program ()) mt]

    [(make_program (stmt_1 stmt_2 ...)) (stmt_1 (make_program (stmt_2 ...)))]
)

(define-metafunction FREEZE
    make_reg : ((var (ty val)) ...) -> reg

    [(make_reg ()) regmt]

    [(make_reg ((var_1 (ty_1 val_1)) (var_2 (ty_2 val_2)) ... )) ((var_1 (ty_1 val_1)) (make_reg ((var_2 (ty_2 val_2)) ...)))]
)

(define-metafunction FREEZE
    make_mem : ((index byte) ...) -> mem

    [(make_mem ()) memmt]

    [(make_mem ((index_1 byte_1) (index_2 byte_2) ...)) ((index_1 byte_1) (make_mem ((index_2 byte_2) ...)))]
)

(define-metafunction FREEZE
    eval : p -> (retty retval) or UB

    [(eval p) (end ,(first (apply-reduction-relation* -->R (term (start p)))))]
)

;(redex-match? FREEZE state (term (((label "entry")
;(((% "trig") = (load (i 16) (ptr (i 16)) (% "p_ptr") )) mt)) (((% "p_ptr") ((ptr (i 16)) poison)) regmt) memmt "" "" mt) ))
;(traces -->R (term (start ((label "entry") (((% "val") = (add nuw (i 16) 65535 1)) ((ret (i 16) (% "val")) ((ret (i 16) (% "val")) mt)))))))
;(term (end ,(first (apply-reduction-relation* -->R (term (((label "entry") (((% "trig") = (load (i 16) (ptr (i 16)) (% "p_ptr") )) mt)) (((% "p_ptr") ((ptr (i 16)) poison)) regmt) memmt "" "" mt))))))
;(traces -->R (term (((store (i 16) 257 (ptr (i 16)) 0) mt) regmt memmt "" "" mt) ) )
;(redex-match? FREEZE stmt (term (br (% "c2") label (% "then") label (% "else"))))



;;;; PRESENTATION INSTRUCTIONS

;; Freezing a poison value ;; Rule fr_poison

(define-term fr_pois_p (
    make_program (
        ((% "a") = (freeze (i 16) poison))
    )
))



;(traces -->R (term (fr_pois_p regmt memmt "" "" mt ())))

;; Freezing 432 ;; Rule fr_val

(define-term fr_nonpois_p (
    make_program (
        ((% "a") = (freeze (i 16) 432))
    )
))

;(traces -->R (term (fr_nonpois_p regmt memmt "" "" mt ())))


;; Freezing a poison pointer -> nondereferenceable  ;; Rules fr_ptr, load_nonderef

(define-term fr_ptr_p (
    make_program (
        ((% "a") = (freeze (ptr (i 16)) poison))
        ((% "b") = (load (i 16) (ptr (i 16)) (% "a")))
    )
))

;(traces -->R (term (fr_ptr_p regmt memmt "" "" mt ())))


;; add nuw overflow   ;; Rules add_nuw_over, ret_ty

(define-term add_poison_p (
    make_program (
        ((% "a") = (add nuw (i 16) 65535 3))   
        (ret (i 16) (% "a"))
    )
)

)

;(traces -->R (term (add_poison_p regmt memmt "" "" mt ())))

;; add nuw without overflow   ;; Rule add_nuw

(define-term add_nonpoison_p (
    make_program (
        ((% "a") = (add nuw (i 16) 40 3))
        (ret (i 16) (% "a"))
    )
)

)

;(traces -->R (term (add_nonpoison_p regmt memmt "" "" mt ())))


;; select poison condition ;; Rule sel_poison

(define-term sel_poison_p (  
    make_program (
        ((% "a") = (select poison (i 16) 10 20))
        (ret (i 16) (% "a"))
    )
)

)

;(traces -->R (term (sel_poison_p regmt memmt "" "" mt ())))


;; select first val  ;; Rule sel_1

(define-term sel_1_p (
    make_program (
        ((% "a") = (select 1 (i 16) 10 poison))
        (ret (i 16) (% "a"))
    )
)

)

;(traces -->R (term (sel_1_p regmt memmt "" "" mt ())))

;; select second val ;; Rule sel_2

(define-term sel_2_p (   
    make_program (
        ((% "a") = (select 0 (i 16) 10 poison))
        (ret (i 16) (% "a"))
    )
)

)
;(traces -->R (term (sel_2_p regmt memmt "" "" mt ())))


;; phi value and non-poison  ;; Rules br_lbl, phi

(define-term phi_poison (
    make_program  (
        (br label (% "first"))

        (label "first")
        (br label (% "end"))

        (label "second")
        (br label (% "end"))

        (label "end")
        ((% "a") = (phi (i 16) [1 "first"] [poison "second"]))
    )
)

)

;(traces -->R (term (phi_poison regmt memmt "" "" phi_poison ())))

;; branching on poison is UB  ;; Rule br_poison

(define-term br_poison (
    make_program (
        (br poison label (% "first") label (% "second"))

        (label "first")
        (ret (i 16) 1)

        (label "second")
        (ret (i 16) 2)
    )
)

)

;(traces -->R (term (br_poison regmt memmt "" "" br_poison ())))


;; Branching on non-poison, both cases ;; Rules br_1, br_2
(define-term br_nonpoison (
    make_program (
        (br 1 label (% "first") label (% "second"))

        (label "first")
        (ret (i 16) 1)

        (label "second")
        (ret (i 16) 2)
    )
)

)

;(traces -->R (term (br_nonpoison regmt memmt "" "" br_nonpoison ())))


;;;; OPTIMIZATION EXAMPLES


;; Loop unswitching original

;   while(c){
;        if(c2){
;            return 2;
;        }else{
;            return 1;
;        }
;    }
;    return 0;

(define-term l_unsw_before
    (make_program 
(
    (label "entry")
    ((% "c") = (add nuw (i 1) 0 0)) ; c is false
    ((% "c2") = (add nuw (i 1) 1 1)) ; c2 is poison
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

;(traces -->R (term (l_unsw_before regmt memmt "" "" l_unsw_before ())))

;; Loop unswitching after, incorrect. Branching on poison is needed for GVN (type of optimization) to be sound


;   if(c_2){
;        while(c){return 2;}
;    }else{
;        while(c){return 1;}
;    }
;    return 0;

(define-term l_unsw_after_wrong(
    make_program (
    (label "entry")
    ((% "c") = (add nuw (i 1) 0 0))
    ((% "c2") = (add nuw (i 1) 1 1))
    (br label (% "if"))

    (label "if")
    (br (% "c2") label (% "then") label (% "else"))

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

;(traces -->R (term (l_unsw_after_wrong regmt memmt "" "" l_unsw_after_wrong ())))

;; Loop unswitching with freeze, now correct (result must be 0)

;   c_fr = freeze(c2);
;   if(c_fr){
;        while(c){return 2;}
;    }else{
;        while(c){return 1;}
;    }
;    return 0;

(define-term l_unsw_after_right(
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

;(traces -->R (term (l_unsw_after_right regmt memmt "" "" l_unsw_after_right ())))



;; Reverse predication before 


(define-term rev_pred_before(
    make_program (
        (label "entry")
        ((% "c") = (add nuw (i 1) 1 1))
        ((% "x") = (select (% "c") (i 16) 100 10))
        (ret (i 16) (% "x"))
    )

)

) 
;(traces -->R (term (rev_pred_before regmt memmt "" "" mt ())))


;; Reverse predication after, incorrect

(define-term rev_pred_after_wrong (
    make_program (
        (label "entry")
        ((% "c") = (add nuw (i 1) 1 1))
        (br (% "c") label (% "true") label (% "false"))

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

;(traces -->R (term (rev_pred_after_wrong regmt memmt "" "" rev_pred_after_wrong ())))

;; Reverse predication after with freeze, now correct

(define-term rev_pred_after_right (
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



;(traces -->R (term (rev_pred_after_right regmt memmt "" "" rev_pred_after_right ())))


;; Load widening reg layout, for both bitwidths

(define-term wid_reg_8 (
    make_reg (
        ((% "ptr") ((ptr (i 8)) 16))
    )
))

(define-term wid_reg_16 (
    make_reg (
        ((% "ptr") ((ptr (i 16)) 16))
    )
)

)
;; Load widening memory layout

(define-term wid_mem (
    make_mem (
        (16 (0 0 0 0 0 1 1 1))
    )
)

)
;; Load widening before, loading 8-bit value

(define-term wid_before (
    make_program (
        ((% "a") = (load (i 8) (ptr (i 8)) (% "ptr")))
        (ret (i 8) (% "a"))
    )
))



;(traces -->R (term (wid_before wid_reg_8 wid_mem"" "" mt ())))

;; Load widening, converting directly to (i 16), incorrect

(define-term wid_after_wrong (
    make_program (
        ((% "a") = (load (i 16) (ptr (i 16)) (% "ptr")))
        (ret (i 16) (% "a"))
    )
))


;(traces -->R (term (wid_after_wrong wid_reg_16 wid_mem "" "" mt ())))


;; Load widening, turning (i 16) into (2 x (i 8)), now correct

(define-term wid_after_right (
    make_program (
        ((% "a_vec") = (load (2 x (i 8)) (ptr (2 x (i 8))) (% "ptr")))
        ((% "a") = (extractelement (2 x (i 8)) (% "a_vec") 0))
        (ret (i 8) (% "a"))
    )
)
)

;(traces -->R (term (wid_after_right wid_reg_8 wid_mem "" "" mt ())))






