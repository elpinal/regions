(ns regions.core
  (:require [hiccup.core :as hiccup]))

(def esop "European Symposium on Programming")
(def fool "Foundations of Object-Oriented Languages")
(def hoots "Higher Order Operational Techniques in Semantics")
(def hosc "Higher-Order and Symbolic Computation")
(def ic "Information and Computation")
(def icalp "ICALP")
(def icfp "ICFP")
(def ifl "Implementation and Application of Functional Languages")
(def ismm "International Symposium on Memory Management")
(def jfp "Journal of Functional Programming")
(def oopsla "Object-oriented Programming, Systems, Languages, and Applications")
(def pldi "PLDI")
(def plilp "Programming Languages Implementation and Logic Programming")
(def popl "Principles of Programming Languages")
(def ppdp "Principles and Practice of Declarative Programming")
(def tapsoft "TAPSOFT")
(def tcs "Theoretical Computer Science")
(def tldi "Types in Language Design and Implementation")
(def toplas "ACM Transactions on Programming Languages and Systems")

(def birkedal "Lars Birkedal")
(def calcagno "Christiano Calcagno")
(def cardelli "Luca Cardelli")
(def crary "Karl Crary")
(def elsman "Martin Elsman")
(def hallenberg "Niels Hallenberg")
(def harper "Robert Harper")
(def helsen "Simon Helsen")
(def henglein "Fritz Henglein")
(def jouvelot "Pierre Jouvelot")
(def leroy "Xavier Leroy")
(def makholm "Henning Makholm")
(def mitchell "John C. Mitchell")
(def moggi "Eugenio Moggi")
(def niss "Henning Niss")
(def talpin "Jean-Pierre Talpin")
(def thiemann "Peter Thiemann")
(def tofte "Mads Tofte")
(def vejlstrup "Magnus Vejlstrup")

(def harvard-cs-group "Harvard Computer Science Group")

(defn write
  [fname x]
  (with-open [w (clojure.java.io/writer fname)]
    (.write w x)))

(defn render
  [{:keys [key title author date location url tr-url slides appendix]}]
  [:div
   [:h4 title]
   [:p author]
   [:p (str (cond
              (sequential? location)
              (apply str (interpose ", " (map #(hiccup/html %) location)))
              (= :manuscript location) "Manuscript"
              :else location)
            (if location ", ") date)]
   (if url
     (into [] (concat
               [:p "Available at "
                [:a {:href url} url]]
               (if tr-url ; Technical Report URL
                 [[:br]
                  "Technical Report: "
                  [:a {:href tr-url} tr-url]]))))
   (if slides
     [:p "Slides: "
      [:a {:href slides} slides]])
   (if appendix
     [:p "Appendix: "
      [:a {:href appendix} appendix]])])

(defn html-entries
  [xs]
  (apply str (interpose "\n" (map #(hiccup/html (render %)) xs))))

(defn authors
  ([x] x)
  ([x & ys]
   (let [l (last (cons x ys))
         xs (butlast (cons x ys))]
     (str (apply str (interpose ", " xs)) " and " l))))

(defn str-pages
  [pages]
  (apply str (interpose \u2013 pages)))

(defn proceedings-location
  [location & {:keys [pages]}]
  (apply str location (if pages [", pp. " (str-pages pages)])))

(defn techrpt-location
  [& {:keys [institution number]}]
  (str institution ", " number))

(defn dissertation-location
  [& {:keys [institution degree]}]
  (str degree " dissertation, " institution))

(defn master-thesis
  [& {:keys [institution]}]
  (str "Master thesis, " institution))

(defn wrap-with-paren
  [x]
  (if x
    (str "(" x ")")))

(defn journal-location
  [title & {:keys [pages volume number]}]
  (if volume
    [[:i title] (str volume (wrap-with-paren number) (if pages (str ", pp. " (str-pages pages))))]
    [[:i title]]))

(defn book-location
  [title & {:keys [publisher pages]}]
  (if publisher
    [[:i title] (str (if pages (str "pp. " (str-pages pages) ", ")) publisher)]
    [[:i title]]))

(def entries
  (array-map
   :tj1992
   {:title    "Polymorphic type, region and effect inference"
    :author   (authors talpin jouvelot)
    :date     1992
    :location (journal-location jfp :volume 2 :number 3)
    :url      "https://www.irisa.fr/prive/talpin/papers/jfp92.pdf"}

   :tt1992
   {:title    "Data region inference for polymorphic functional languages"
    :author   (authors tofte talpin)
    :date     1992
    :location :manuscript}

   :tt1993
   {:title    "A theory of stack allocation in polymorphically typed languages"
    :author   (authors tofte talpin)
    :date     1993
    :month    :july
    :location (techrpt-location :institution "University of Copenhagen" :number "93/15")
    :url      "http://elsman.com/mlkit/pdf/93.15.pdf"}

   :tt1994
   {:title    "Implementation of the typed call-by-value λ-calculus using a stack of regions"
    :author   (authors tofte talpin)
    :date     1994
    :location (proceedings-location popl)
    :url      "http://elsman.com/mlkit/pdf/popl94.pdf"}

   :vej1994
   {:title    "Multiplicity inference"
    :author   vejlstrup
    :date     1994
    :location (master-thesis :institution "University of Copenhagen")
    :url      "http://elsman.com/mlkit/pdf/magnus.pdf"}

   :btv1996
   {:title    "From region inference to von Neumann machines via region representation inference"
    :author   (authors birkedal tofte vejlstrup)
    :date     1996
    :month    :january
    :location (proceedings-location popl)
    :url      "http://elsman.com/mlkit/pdf/popl96.pdf"}

   :tt1997
   {:title    "Region-based memory management"
    :author   (authors tofte talpin)
    :date     1997
    :location (journal-location "Information and Computation" :volume 132 :number 2 :pages '(109 176))
    :url      "https://doi.org/10.1006/inco.1996.2613"}

   :thi1997
   {:title    "Correctness of a region-based binding-time analysis"
    :author   thiemann
    :date     1997
    :location (journal-location "Electronic Notes in Theoretical Computer Science" :volume 6 :pages '(365 390))
    :url      "https://doi.org/10.1016/S1571-0661(05)80148-3"}

   :tb1998
   {:title    "A region inference algorithm"
    :author   (authors tofte birkedal)
    :date     1998
    :location (journal-location toplas :volume 20 :number 4 :pages '(724 767))
    :url      "http://elsman.com/mlkit/pdf/toplas98.pdf"}

   :tof1998
   {:title    "A brief introduction to regions"
    :author   tofte
    :date     1998
    :location (proceedings-location ismm)
    :url      "http://elsman.com/mlkit/pdf/ismm98.pdf"}

   :tb2000
   {:title    "Unification and polymorphism in region inference"
    :author   (authors tofte birkedal)
    :date     2000
    :location (book-location "Proof, Language, and Interaction. Essays in Honour of Robin Milner" :publisher "MIT Press")
    :url      "http://www.cs.au.dk/~birke/papers/unipri.ps.gz"}

   :ht2000
   {:title    "Syntactic type soundness for the region calculus"
    :author   (authors helsen thiemann)
    :date     2000
    :month    :september
    :location (proceedings-location hoots :pages '(1 20))
    :url      "https://doi.org/10.1016/S1571-0661(04)80870-3"}

   :bt2001
   {:title    "A constraint-based region inference algorithm"
    :author   (authors birkedal tofte)
    :date     2001
    :month    :may
    :location (journal-location tcs :volume 258 :number 1 :pages '(299 392))
    :url      "http://www.cs.au.dk/~birke/papers/conria.ps.gz"}

   :cht2002
   {:title    "Syntactic type soundness results for the region calculus"
    :author   (authors calcagno helsen thiemann)
    :date     2002
    :month    :march
    :location (journal-location ic :volume 173 :number 2 :pages '(199 221))
    :url      "https://doi.org/10.1006/inco.2001.3112"}

   :eh2002
   {:title    "A region-based abstract machine for the ML Kit"
    :author   (authors elsman hallenberg)
    :date     2002
    :month    :august
    :location (techrpt-location :institution "IT University of Copenhagen" :number "TR-2002-18")
    :url      "http://elsman.com/mlkit/pdf/kam.pdf"}

   :mak2003
   {:title    "A language-independent framework for region inference"
    :author   makholm
    :date     2003
    :month    :august
    :location (dissertation-location :institution "University of Copenhagen" :degree "PhD")
    :url      "http://henning.makholm.net/misc/thesis.pdf"}

   :tbeh2004
   {:title    "A retrospective on region-based memory management"
    :author   (authors tofte birkedal elsman hallenberg)
    :date     2004
    :location (journal-location hosc :volume 17 :number 3 :pages '(245 265))
    :url      "http://elsman.com/mlkit/pdf/retro.pdf"}

   :hel2004
   {:title    "Bisimilarity for the region calculus"
    :author   helsen
    :date     2004
    :location (journal-location hosc :volume 17 :number 4 :pages '(347 394))
    :url      "https://www.researchgate.net/publication/220606930_Bisimilarity_for_the_Region_Calculus"}

   :hmn2005
   {:title    "Effect types and region-based memory management"
    :author   (authors henglein makholm niss)
    :date     2005
    :location (book-location "Advanced topics in types and programming languages" :publisher "MIT Press" :pages '(87 136))}
   ))

(defn -main
  []
  (write "../README.md" (str "# Regions\n\n"
                             "## Implementations\n\n"
                             "- `src/tt1994.rs`: the target language of Tofte and Talpin (1994)\n\n"
                             "## Incomplete Bibliography of Region-based Memory Management\n\n"
                             (html-entries (vals entries)))))
