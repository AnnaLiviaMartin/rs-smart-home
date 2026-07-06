//Allergröbstes Modell
sig RAUM {
var	personenImRaum: set PERSON,
	id: Int,
	nachbarn: some RAUM
}

pred mindestensZweiRaume{
	#RAUM >= 2
}

pred raeumeEindeutigIdentifizierbar {
	all disj r1, r2: RAUM | r1.id != r2.id
}

pred raumIstNichtEigenerNachbar {
	all r: RAUM | r not in r.nachbarn
}

pred nachbarnSindSymmetrisch {
	all r1, r2: RAUM | r1 in r2.nachbarn <=> r2 in r1.nachbarn
}

pred keineRaumInseln{
	all r1, r2: RAUM | r1 != r2 implies r2 in r1.^nachbarn
}

// Gröbstes Modell
sig PERSON {}

pred einePersonInGenauEinemRaum {
	always (all p: PERSON |
		#(p.~personenImRaum) = 1	
	)
}

pred raumWechseln [p: PERSON, r1, r2: RAUM]{
	//pre
	r1 != r2
	r2 in r1.nachbarn
	p in r1.personenImRaum

	//post
	r1.personenImRaum' = r1.personenImRaum - p
	r2.personenImRaum' = r2.personenImRaum + p

	//frameCondition, damit sich die anderen Räume nicht ändern
	all r: RAUM - (r1 + r2) | r.personenImRaum' = r.personenImRaum
}

pred stutter{
	all r: RAUM | r.personenImRaum' = r.personenImRaum
}

pred show{
	raeumeEindeutigIdentifizierbar
	mindestensZweiRaume
	raumIstNichtEigenerNachbar
	nachbarnSindSymmetrisch
	keineRaumInseln
	einePersonInGenauEinemRaum

	always some p: PERSON, r1, r2: RAUM | raumWechseln[p, r1, r2]
//	or stutter
}

run show 
