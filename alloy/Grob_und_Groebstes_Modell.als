//Gröbstes Modell
sig PERSON {}

sig RAUM {
var	personenImRaum: set PERSON,
	id: Int,
	nachbarn: some RAUM
}

pred mindestensZweiRaume{
	#RAUM >= 2
}

pred raumIstNichtEigenerNachbar {
	always (
		all r: RAUM | r not in r.nachbarn
	)
}

pred nachbarnSindSymmetrisch {
	always (
		all r1, r2: RAUM | r1 in r2.nachbarn <=> r2 in r1.nachbarn
	)
}

// Gröbstes Modell
pred einePersonInGenauEinemRaum {
	always (all p: PERSON |
		#(p.~personenImRaum) = 1	
	)
}

pred personenKoennenNurZwischenNachbarnWechseln {
	always (
		all p: PERSON, r1, r2: RAUM |
			(p in r1.personenImRaum and p in r2.personenImRaum' and r1 != r2)
			implies r2 in r1.nachbarn
	)
}

pred show{
	mindestensZweiRaume
	raumIstNichtEigenerNachbar
	nachbarnSindSymmetrisch
	einePersonInGenauEinemRaum
	personenKoennenNurZwischenNachbarnWechseln
}

run show 
