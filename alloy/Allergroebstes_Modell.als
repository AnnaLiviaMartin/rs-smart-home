//Allergröbstes Modell
sig RAUM {
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

pred show{
	raeumeEindeutigIdentifizierbar
	mindestensZweiRaume
	raumIstNichtEigenerNachbar
	nachbarnSindSymmetrisch
	keineRaumInseln	
}

run show for exactly 5 RAUM
