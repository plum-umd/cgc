-- Note: the default Agda fixity is 20 non-associative...

------------
-- SYNTAX --
------------

-- 0: low precedence dollar, keying off do notation, do notation separator
--   (R) _$$_ do_ _‣_
-- 1: dollar and if
--   (R) _$_ if_else_then_
-- 2: dependent tuples
--   (R) ∃_,,_
-- 3: tuples
--   (R) _,_
-- 4: infix words
--   (L) _𝑎𝑡_ _𝑜𝑛_

-----------
-- TYPES --
-----------

-- 10: existentials
--   (R) ∃_𝑠𝑡_ ∃_⦂_𝑠𝑡_
-- 11: type exponentials
--   (R) _↔_ _⇉_
-- 12: type sums
--   (R) _∨_
-- 13: type products
--   (R) _∧_
-- 14: relations
--   _≡_ _⊑_ _∈_

-----------
-- TERMS --
-----------

-- 22: term sums
--   (R) _+_ _⧺_
-- 23: term sum difference
--   _-_
-- 24: term products
--   (R) _×_
-- 25: term product difference
--  _/_

-----------
-- OTHER --
-----------

-- 30: composition
--   (R) _∘_ _⊚_
-- 40: constructors 
--   (R) _∷_ 
-- 50: application
--   (L) _⋅_
-- 60: negation and extension
--   (R) ⁻_ _*
