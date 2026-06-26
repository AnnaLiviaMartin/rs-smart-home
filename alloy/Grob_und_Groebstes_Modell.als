//Gröbstes Modell
sig PERSON {}

sig RAUM {
var	personenImRaum: set PERSON,
	id: Int,
	nachbarn: some RAUM
}

fact mindestensZweiRaume{
	#RAUM >= 2
}

fact raumIstNichtEigenerNachbar {
	always (
		all r: RAUM | r not in r.nachbarn
	)
}

fact nachbarnSindSymmetrisch {
	always (
		all r1, r2: RAUM | r1 in r2.nachbarn <=> r2 in r1.nachbarn
	)
}

// Gröbstes Modell
fact einePersonInGenauEinemRaum {
	always (all p: PERSON |
		#(p.~personenImRaum) = 1	
	)
}

fact personenKoennenNurZwischenNachbarnWechseln {
	always (
		all p: PERSON, r1, r2: RAUM |
			(p in r1.personenImRaum and p in r2.personenImRaum' and r1 != r2)
			implies r2 in r1.nachbarn
	)
}

run {} 
