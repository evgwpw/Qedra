; group.lisp — тесты шага G1.1: перестановки, орбиты, Шрайер — Симс, сертификат BSGS.

(deftest "G1: perm-from-cycles/perm->cycles — туда и обратно"
  (assert-equal (perm->cycles (perm-from-cycles '((1 2 3) (4 5))))
                '((1 2 3) (4 5))))

(deftest "G1: порядок и знак перестановки"
  (assert-equal (perm-order (perm-from-cycles '((1 2 3) (4 5)))) 6)
  (assert-equal (perm-sign (perm-from-cycles '((1 2 3) (4 5)))) -1)
  (assert-equal (perm-sign (perm-from-cycles '((1 2 3)))) 1))

(deftest "G1: произведение по конвенции GAP (сначала левый)"
  ; p=(1 2 3), q=(2 3): (p·q)(i)=q(p(i)) → 1↦q(2)=3, 2↦q(3)=2, 3↦q(1)=1 → (1 3)
  (assert-equal (perm->cycles (perm-mul (perm-from-cycles '((1 2 3)))
                                        (perm-from-cycles '((2 3)))))
                '((1 3))))

(deftest "G1: обратная и тождественность"
  (assert-true (perm-identity? (perm-mul (perm-from-cycles '((1 2 3) (4 5)))
                                         (perm-inv (perm-from-cycles '((1 2 3) (4 5)))))))
  (assert-true (perm-identity? (perm-id 5))))

(deftest "G1: орбита точки под S5"
  (assert-equal (sort (group-orbit (list (perm-from-cycles '((1 2)))
                                         (perm-from-cycles '((1 2 3 4 5)))) 3)
                      (lambda (a b) (< a b)))
                '(1 2 3 4 5)))

(deftest "G1: |S5| = 120, принадлежность и сертификат"
  (let ((S5 (list (perm-from-cycles '((1 2))) (perm-from-cycles '((1 2 3 4 5))))))
    (assert-equal (group-order (list S5 5)) 120)
    (assert-true (group-member? (list S5 5) (perm-from-cycles '((1 2 3 4)))))
    (assert-true (bsgs-check (list S5 5) #f))))

(deftest "G1: |A5| = 60, нечётная перестановка не входит"
  (let ((A5 (list (perm-from-cycles '((1 2 3))) (perm-from-cycles '((1 2 3 4 5))))))
    (assert-equal (group-order (list A5 5)) 60)
    (assert-equal (group-member? (list A5 5) (perm-from-cycles '((1 2)))) #f)))

(deftest "G1: |D6| = 6 на трёх точках и |C5| = 5"
  (let ((D6 (list (perm-from-cycles '((1 2 3))) (perm-from-cycles '((1 2))))))
    (assert-equal (group-order (list D6 3)) 6))
  (let ((C5 (list (perm-from-cycles '((1 2 3 4 5))))))
    (assert-equal (group-order (list C5 5)) 5)))

(deftest "G1: |M11| = 7920 (ATLAS), сертификат BSGS"
  (let ((M11 (list (perm-from-cycles '((1 2 3 4 5 6 7 8 9 10 11)))
                   (perm-from-cycles '((3 7 11 8) (4 10 5 6))))))
    (assert-equal (group-order (list M11 11)) 7920)
    (assert-true (bsgs-check (list M11 11) #f))))

(deftest "G1: группа кубика 2×2×2 — |G| = 3 674 160"
  ; 24 точки = 8 углов × 3 ориентации (индекс 3p+o); повороты U, R, F;
  ; порядок карманного кубика 8!·3⁷/24 (без фиксации куба в пространстве)
  (let ((U (cube-move '((1 4 3 2)) '(0 0 0 0 0 0 0 0)))
        (R (cube-move '((1 5 8 4)) '(2 0 0 1 1 0 0 2)))
        (F (cube-move '((1 2 6 5)) '(1 2 0 0 2 1 0 0))))
    (assert-equal (group-order (list (list U R F) 24)) 3674160)))

(deftest "G1: подделка BSGS — убран уровень, порядок занижен"
  ; строим систему для S5, удаляем уровень 2 целиком — шрайеровские генераторы
  ; уровня 1 перестают просеиваться (их стабилизатор не покрыт) → сертификат #f
  (let* ((S5 (list (perm-from-cycles '((1 2))) (perm-from-cycles '((1 2 3 4 5)))))
         (G (list S5 5))
         (bsgs (group-bsgs S5 5))
         (broken (list (car bsgs)
                       (list (nth (cadr bsgs) 0) (nth (cadr bsgs) 2)))))
    (assert-true (bsgs-check G bsgs))
    (assert-equal (bsgs-check G broken) #f)))

(deftest "G1: стабилизатор точки — лемма Шрайера (все генераторы фиксируют точку)"
  (let* ((S5 (list (perm-from-cycles '((1 2))) (perm-from-cycles '((1 2 3 4 5)))))
         (stab (group-stabilizer-gens S5 1)))
    ; все генераторы стабилизатора фиксируют точку 1 и принадлежат S5
    (assert-true (all-fix? stab 0))
    (assert-true (all-member? (list S5 5) stab))))

; ---------- G1.2: смежные классы, стандартные группы, Тодд — Коксетер ----------

(deftest "G1.2: стандартные группы — порядки"
  (assert-equal (group-order (symmetric-group 5)) 120)
  (assert-equal (group-order (symmetric-group 6)) 720)
  (assert-equal (group-order (alternating-group 5)) 60)
  (assert-equal (group-order (alternating-group 6)) 360)
  (assert-equal (group-order (alternating-group 4)) 12)
  (assert-equal (group-order (dihedral-group 3)) 6)
  (assert-equal (group-order (dihedral-group 4)) 8)
  (assert-equal (group-order (dihedral-group 5)) 10)
  (assert-equal (group-order (cyclic-group 5)) 5))

(deftest "G1.2: смежные классы — |C4| в S5: индекс 30, A5 в S5: индекс 2"
  (let ((S5 (list (list (perm-from-cycles '((1 2))) (perm-from-cycles '((1 2 3 4 5)))) 5))
        (H (list (list (perm-from-cycles '((2 3 4 5)))) 5)))
    (assert-true (group-subgroup? S5 H))
    (assert-equal (group-index S5 H) 30)
    (assert-equal (length (group-cosets S5 H)) 30))
  (let ((S5 (symmetric-group 5)) (A5 (alternating-group 5)))
    (assert-true (group-subgroup? S5 A5))
    (assert-equal (group-index S5 A5) 2)
    (assert-equal (length (group-cosets S5 A5)) 2)))

(deftest "G1.2: не подгруппа — индекс #f, классы not-subgroup"
  (let ((S5 (symmetric-group 5)) (A5 (alternating-group 5)))
    (assert-equal (group-index A5 S5) #f)
    (assert-equal (group-cosets A5 S5) 'not-subgroup)))

(deftest "G1.2: Тодд — Коксетер: ⟨a,b | a², b³, (ab)⁵⟩ → 60 (A5)"
  (let ((r (coset-enumerate '(a b) '((a a) (b b b) (a b a b a b a b a b)) '() 200)))
    (assert-equal (nth r 1) 60)
    (assert-true (coset-table-check '(a b) '((a a) (b b b) (a b a b a b a b a b)) '() r))))

(deftest "G1.2: Тодд — Коксетер: ⟨a,b | a³, b², (ab)²⟩ → 6 (S3)"
  (let ((r (coset-enumerate '(a b) '((a a a) (b b) (a b a b)) '() 50)))
    (assert-equal (nth r 1) 6)
    (assert-true (coset-table-check '(a b) '((a a a) (b b) (a b a b)) '() r))))

(deftest "G1.2: Тодд — Коксетер: ⟨a | a⁷⟩ → 7; инверсные буквы"
  (let ((r (coset-enumerate '(a) '((a a a a a a a)) '() 20)))
    (assert-equal (nth r 1) 7)
    (assert-true (coset-table-check '(a) '((a a a a a a a)) '() r)))
  ; (inv a) в словах: (ab)² записано как (ab)^2 через инверсии
  (let ((r (coset-enumerate '(a b) '((a a a) (b b) ((inv a) (inv b) (inv a) (inv b))) '() 50)))
    (assert-equal (nth r 1) 6)))

(deftest "G1.2: Тодд — Коксетер: подгруппа ⟨a⟩ в A5 → индекс 30"
  (let ((r (coset-enumerate '(a b) '((a a) (b b b) (a b a b a b a b a b)) '((a)) 200)))
    (assert-equal (nth r 1) 30)
    (assert-true (coset-table-check '(a b) '((a a) (b b b) (a b a b a b a b a b)) '((a)) r))))

(deftest "G1.2: Тодд — Коксетер: переполнение → unknown"
  (assert-equal (coset-enumerate '(a b) '((a a a) (b b) (a b a b)) '() 5) 'unknown))


(deftest "G1: подделка BSGS — система подгруппы (A5) или надгруппы (S5) не сертифицирует другую группу"
  (let* ((S5 (list (list (perm-from-cycles '((1 2))) (perm-from-cycles '((1 2 3 4 5)))) 5))
         (A5 (list (list (perm-from-cycles '((1 2 3))) (perm-from-cycles '((1 2 3 4 5)))) 5)))
    (assert-equal (bsgs-check S5 (group-bsgs (car A5) 5)) #f)
    (assert-equal (bsgs-check A5 (group-bsgs (car S5) 5)) #f)
    (assert-true (bsgs-check A5 (group-bsgs (car A5) 5)))))

(deftest "G1.2: Тодд — Коксетер — бесконечный индекс (образующий вне соотношений) → unknown, не ложный индекс"
  (assert-equal 'unknown (coset-enumerate '(a) '() '() 50))
  (assert-equal 'unknown (coset-enumerate '(a b) '((a a)) '() 50))
  ; S4 = ⟨a, b | a², b³, (ab)⁴⟩, A4 = ⟨a, b | a², b³, (ab)³⟩
  (let ((r (coset-enumerate '(a b) '((a a) (b b b) (a b a b a b a b)) '() 100)))
    (assert-equal 24 (cadr r))
    (assert-true (coset-table-check '(a b) '((a a) (b b b) (a b a b a b a b)) '() r)))
  (assert-equal 12 (cadr (coset-enumerate '(a b) '((a a) (b b b) (a b a b a b)) '() 100))))
