sig PERSON {}
sig RAUM {
	id: Int,
	nachbarn: some TUER,
var	personenImRaum: set PERSON
}

sig ZIMMER extends RAUM{
	authentication: one AUTHENTICATION,
}

sig GARTEN extends RAUM{
}{
	one nachbarn //Garten soll nur einen Zugang zum Haus haben
}

sig AUTHENTICATION{
	authentifiziertePersonen: some PERSON
}

sig TUER {
	nachbarn: set RAUM
}

pred einePersonInGenauEinemRaum {
	always (all p: PERSON |
		#(p.~personenImRaum) = 1	
	)
}

pred tuerVerbindetZweiRaeume {
    all t: TUER | #t.nachbarn = 2
}

pred raeumeEindeutigIdentifizierbar { //bruacht man stand jetzt nicht?
	all disj r1, r2: RAUM | r1.id != r2.id
}

pred alleNachbarnSindSymmerisch {
	all r: RAUM, t: TUER | r in t.nachbarn <=> t in r.nachbarn
	all t:TUER, r: RAUM | t in r.nachbarn <=> r in t.nachbarn
}

pred init {
	all p: PERSON | p in GARTEN.personenImRaum
}

pred show {
init
tuerVerbindetZweiRaeume
alleNachbarnSindSymmerisch
einePersonInGenauEinemRaum
}

run show for exactly 2 PERSON, exactly 2 ZIMMER, exactly 1 GARTEN, 2 AUTHENTICATION, 2 TUER, 3 RAUM
