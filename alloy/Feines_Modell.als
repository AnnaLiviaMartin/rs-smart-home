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
	darfBetreten[p, r2]

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

// Feines Modell
/*
- Eine Person kann entweder ein Gast oder ein Bewohner sein.
- Ein Bewohner ist eine Person, die mindestens einen Raum besitzt.
- Alle Personen haben immer in freie Räume zutritt.
- Begleiträume dürfen von Gästen nur betreten werden, wenn ein Bewohner in diesem Raum ist.
- Privaträume dürfen nur vom jeweiligen Bewohner/Besitzer des Raumes betreten werden.
*/

abstract sig PERSON {}

sig GAST extends PERSON {}
sig BEWOHNER extends PERSON {
	besitzt: set RAUM,
 	besitztMaxRaeume: Int
}

abstract sig RAUM {
	var	personenImRaum: set PERSON,
	id: Int,
	nachbarn: some RAUM,
	maxPersonenInRaum: Int,
	maxBesitzerFuerRaum: Int
}

sig FREIERRAUM extends RAUM {}
sig PRIVATRAUM extends RAUM {}
sig BEGLEITRAUM extends RAUM {}

pred darfFreienRaumBetreten [p: PERSON, r: RAUM] {
	(r in FREIERRAUM) and ((p in GAST) or (p in BEWOHNER))
}

pred darfPrivatenRaumBetreten [p: PERSON, r: RAUM] {
	(r in PRIVATRAUM) and p in BEWOHNER and r in p.besitzt
}

pred darfBegleitRaumBetreten [p: PERSON, r: RAUM] {
	(r in BEGLEITRAUM) and (
	    p in BEWOHNER
	    or (p in GAST and some b: BEWOHNER | b in r.personenImRaum)
	  )
}

pred darfBetreten [p: PERSON, r: RAUM] {
	darfFreienRaumBetreten[p, r] or darfPrivatenRaumBetreten[p, r] or darfBegleitRaumBetreten[p, r]
}

pred privaterRaumHatBesitzer {
  always all r: PRIVATRAUM | some p: BEWOHNER | r in p.besitzt
}

pred bewohnerBesitztMindestensEinenRaum {
	 all p: BEWOHNER | #(p.besitzt) >= 1
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
	// Feines Modell
	bewohnerBesitztMindestensEinenRaum
	privaterRaumHatBesitzer
	always all p: PERSON, r: RAUM | p in r.personenImRaum implies darfBetreten[p, r]
}

run show for exactly 5 RAUM, 4 PERSON,  6 Int
