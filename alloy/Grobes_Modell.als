//Allergröbstes Modell
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
	#(r1.personenImRaum) <= r1.maxPersonenInRaum
	#(r2.personenImRaum) <= r2.maxPersonenInRaum

	//post
	r1.personenImRaum' = r1.personenImRaum - p
	r2.personenImRaum' = r2.personenImRaum + p
	#(r2.personenImRaum') <= r2.maxPersonenInRaum
	#(r1.personenImRaum') <= r1.maxPersonenInRaum

	//frameCondition, damit sich die anderen Räume nicht ändern
	all r: RAUM - (r1 + r2) | r.personenImRaum' = r.personenImRaum
}

pred stutter{
	all r: RAUM | r.personenImRaum' = r.personenImRaum
}

// Grobes Modell
sig RAUM {
	var	personenImRaum: set PERSON,
	id: Int,
	nachbarn: some RAUM,
	maxBesitzerFuerRaum: Int,
	maxPersonenInRaum: Int
}

sig PERSON {
	besitzt: set RAUM,
 	besitztMaxRaeume: Int
}

pred RaumNurVonYPersonenBesessen {
	all r: RAUM | r.maxBesitzerFuerRaum >= 0 and r.maxBesitzerFuerRaum <= 5
}

pred PersonNurXRaeumeBesitzen {
	all p: PERSON | p.besitztMaxRaeume >= 0 and p.besitztMaxRaeume <= 5
}

pred RaumKannNurZPersonenFassen {
	all r: RAUM | r.maxPersonenInRaum >= 0 and r.maxPersonenInRaum <= 5
}

pred KapazitaetenEingehalten {
	all r: RAUM | #(r.personenImRaum) <= r.maxPersonenInRaum
	all p: PERSON | #(p.besitzt) <= p.besitztMaxRaeume
}

pred BesitzLimitiertProRaum {
  all r: RAUM | #(r.~besitzt) <= r.maxBesitzerFuerRaum
}

pred show{
	// Allergroebstes Modell
	raeumeEindeutigIdentifizierbar
	mindestensZweiRaume
	raumIstNichtEigenerNachbar
	nachbarnSindSymmetrisch
	keineRaumInseln
	// Groebstes Modell
	einePersonInGenauEinemRaum
	always some p: PERSON, r1, r2: RAUM | raumWechseln[p, r1, r2]
//	or stutter
	// Grobes Modell
	RaumNurVonYPersonenBesessen
	PersonNurXRaeumeBesitzen
	RaumKannNurZPersonenFassen
	KapazitaetenEingehalten
	BesitzLimitiertProRaum
}

run show for exactly 5 RAUM, 8 PERSON,  6 Int
