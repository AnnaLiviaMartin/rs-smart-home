import Mathlib.Tactic
-- Bitte inhalt löschen und mit eigenen code füllen!!!


-- axiom axm0_1 : d in N
axiom d : Int -- d ist eine Ganze Zahl
axiom axm0_2 : d > 0

#check axm0_2 -- aufrufen, falls ich vergessen habe, was in dem axiom stand
#check 4

-- @grind sagt aus, dass das von grind ausgepackt werden darf? Wird in grind DB geschrieben??
@[grind]def inv0_1 (n : Int) := n >= 0 -- backslash gt für größer glcih
def inv0_2 (n : Int) : Prop := n <= d -- man definiert eine ivariante als funktion, die sagt, ob Bedingung erfüllt ist

#check inv0_1

-- ist ein prädikat
def init (n' : Int) := n' = 0

def init_post (n' : Int) := n' = 0 -- int ist nur ein anderes symbol für ℤ

def MLout_pre (n : Int) := n < d --KFZ fährt von Inselbrücke runter
