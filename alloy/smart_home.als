abstract sig Bool {}
one sig True, False extends Bool {}

//#################### Objekte

abstract sig PERSON{}

sig BEWOHNER extends PERSON {}

sig GAST extends PERSON {}

abstract sig ORT {
	var personenImOrtGrob: set PERSON,
	var personenImOrtFein: set PERSON,
	nachbarn: some ORT
}

sig RAUM extends ORT {}{
	nachbarn in TUER
}

sig GARTEN extends RAUM{}{
	one nachbarn
}

sig TUER extends ORT{
	var	offen: one Bool
}{
	nachbarn in RAUM
}

//#################### Axiome

fact genauEinenGarten {
	#GARTEN = 1
}

fact alleRaumeInEinemGebaeude {
	all r: RAUM | r in GARTEN.^nachbarn
}

fact einePersonInGenauEinemOrt {
	always (all p: PERSON |
		#(p.~personenImOrtGrob) = 1	and
		#(p.~personenImOrtFein) = 1
	)
}

fact tuerImmerOffenWennPersonEnthalten{
	always all t: TUER |  #(t.personenImOrtFein) >= 1 implies t.offen = True
}

fact alleNachbarnSindSymmetrisch {
	all r: RAUM, t: TUER | r in t.nachbarn <=> t in r.nachbarn
	all t:TUER, r: RAUM | t in r.nachbarn <=> r in t.nachbarn
}

fact tuerVerbindetZweiRaeume {
    all t: TUER | #t.nachbarn = 2
}

//################## Init #################

pred init {
	all p: PERSON | p in GARTEN.personenImOrtGrob
	all p: PERSON | p in GARTEN.personenImOrtFein
	all t: TUER | t.offen = False
}

//#################### Zustandsübergänge / Ereignisse des Groben Modells

pred schrittGrob[p: PERSON, von, nach: RAUM]{

	//pre --> Verfeinerungsschritte stellen pre-Conditions bereits sicher, daher auskommentiert
//	p in von.personenImOrtGrob
	von != nach
//	some t: TUER | t in von.nachbarn and t in nach.nachbarn and t.offen in True

	//post
	von.personenImOrtGrob' = von.personenImOrtGrob - p
	nach.personenImOrtGrob' = nach.personenImOrtGrob + p

	//frame
	all o: ORT - (von + nach) | o.personenImOrtGrob' = o.personenImOrtGrob
}

//#################### Zustandsübergänge / Ereignisse des Feinen Modells

pred betreteTuer[p: PERSON, von: RAUM, t: TUER]{
	//pre
	p in von.personenImOrtFein
	t in von.nachbarn
	t.offen in True
	//nur eine Person darf die Tür betreten
	#(t.personenImOrtFein) = 0

	//post
	von.personenImOrtFein' = von.personenImOrtFein - p
	t.personenImOrtFein' = t.personenImOrtFein + p

	//frame
	all o: ORT - (von + t) | o.personenImOrtFein' = o.personenImOrtFein
}

pred verlasseTuer[p: PERSON, nach: RAUM, t: TUER]{
	//pre
	p in t.personenImOrtFein
	nach in t.nachbarn

	//post
	t.personenImOrtFein' = t.personenImOrtFein - p
	nach.personenImOrtFein' = nach.personenImOrtFein + p

	//frame
	all o: ORT - (nach + t) | o.personenImOrtFein' = o.personenImOrtFein
}

pred vorbedingungenMoveFein [r1, r2: RAUM, t: TUER] {
	r1 != r2
	r1 in t.nachbarn
	r2 in t.nachbarn
}

pred schrittFein {
	some p: PERSON, r1, r2: RAUM, t: TUER | 
		((betreteTuer[p, r1, t] and StutterSchritt_2) or 
		(verlasseTuer[p, r2, t] and schrittGrob[p, r1, r2])) and 
		vorbedingungenMoveFein[r1, r2, t]
}

//#################### Zustandsübergänge / Ereignisse des Feinen Modells mit Autorisierung

pred schrittSehrFein {
	some p: PERSON, t: TUER |
		(oeffneTuer[p, t] and StutterSchritt_1) or (schrittFein and tuerBleibtOffenOderFaelltZu)	
}

pred oeffneTuer [p: PERSON, tuer: TUER] {
	//pre
	p in BEWOHNER
	tuer in p.~personenImOrtFein.nachbarn //Tür muss nachbar zum Raum sein, in dem die person sich aufhält
	tuer.offen = False

	//post
	tuer.offen' = True
	all t: TUER - tuer | t.offen = False implies t.offen' = False 
}

fact show {
	init
	always schrittSehrFein 
}

run {} for exactly 2 PERSON, 1 GAST, 1 BEWOHNER, exactly 1 GARTEN, exactly 3 TUER, exactly 4 RAUM

//################ Stutter ######################

pred StutterSchritt_1 {
	all o: ORT | o.personenImOrtFein' = o.personenImOrtFein
	all o: ORT | o.personenImOrtGrob' = o.personenImOrtGrob
}

pred StutterSchritt_2{
	all o: ORT | o.personenImOrtGrob' = o.personenImOrtGrob
}

pred tuerBleibtOffenOderFaelltZu {
	all t: TUER | t.offen = False implies t.offen' = False 
}

//################ Tests ######################

assert personNurInEinemOrt {
	always all p: PERSON |
		#(p.~personenImOrtFein) = 1
}

assert geschlosseneTuerIstLeer {
	always all t: TUER |
		t.offen = False implies no t.personenImOrtFein and no t.personenImOrtGrob
}

//Es darf nur eine offene Tür betreten werden
assert bewegungDurchOffeneTuer {
	always all p: PERSON, t: TUER |
		p in t.personenImOrtFein implies t.offen = True
}

assert keineTeleportation_GROB {
	always all p: PERSON, von, nach: ORT | 
		(p in von.personenImOrtGrob and 
		p in nach.personenImOrtGrob' implies 
		(nach in von.nachbarn.nachbarn)) or (p in von.personenImOrtGrob and p in von.personenImOrtGrob')
}

assert keineTeleportation_FEIN {
	always all p: PERSON, von, nach: ORT | 
		(p in von.personenImOrtFein and p in nach.personenImOrtFein' implies (nach in von.nachbarn)) or
		(p in von.personenImOrtFein and p in von.personenImOrtFein')
}

assert personIstNieInTuer_GROB {
	always all p: PERSON, t: TUER |
	(p not in t.personenImOrtGrob)
}

assert personenImGrobmodellNurInRaeumen{
	always all t: TUER | no t.personenImOrtGrob
}

//Prüft allgemeine Gleichheit des Groben und Feinen Modells
assert gleichesErgebnisInFreinUndGrob{
	always all p: PERSON, von: ORT |
		(p in von.personenImOrtGrob and p in von.personenImOrtFein) implies //Beide Personen befinden sich im Raum
		(p in von.personenImOrtGrob' and p in von.personenImOrtFein') or // Personen bleiben im selben Raum
		(p in von.personenImOrtGrob' and p in von.nachbarn.personenImOrtFein') or //hat im feinen Modell eine Tür betreten, bleibt im Groben Modell im Raum
		(p in von.nachbarn.nachbarn.personenImOrtGrob' and p in von.nachbarn.nachbarn.personenImOrtFein')// beide haben den Nachbarraum Betreten
}

// Prüfen, dass wenn sich eine Person von r1 nach r2 im Feinen Modell bewegt, dass das gleiche auch im Groben Modell funktioniert
assert verfeinerungKorrekt { 
	always all p: PERSON, r1, r2: RAUM |
		(p in r1.personenImOrtFein and p in r2.personenImOrtFein')
		implies (p in r1.personenImOrtGrob' and p in r2.personenImOrtGrob')
}

//Personen die sich im Feinen Modell in einem Raum befinden, befinden sich im Groben Modell immer im selben Raum
assert verfeinerungGrobUndFein {
	always all p: PERSON, r: RAUM |
		p in r.personenImOrtFein implies p in r.personenImOrtGrob
}

assert esBefindetSichImmerNurEinePersonInTuer{
	always all t: TUER | #t.personenImOrtFein <= 1
}

assert nurBewohnerKannTuerOeffnen {
	always all t: TUER |
		t.offen = False and t.offen' = True
		implies some b: BEWOHNER |
		b in t.nachbarn.personenImOrtFein
}

assert raumStrukturBleibtGleich {
	always all r: RAUM | 
		r.nachbarn' = r.nachbarn
}

assert tuerStrukturBleibtGleich {
	always all t: TUER | 
		t.nachbarn' = t.nachbarn
}

// Soll Gegenbeispiel liefern, weil Türen zufallen sollen
assert alleTuerenSindImmerOffen {
	always all t: TUER | t.offen = True
}

check personNurInEinemOrt for 5
check geschlosseneTuerIstLeer for 5
check bewegungDurchOffeneTuer for 5
check keineTeleportation_GROB for 5
check personenImGrobmodellNurInRaeumen for 5
check keineTeleportation_FEIN for 5
check personIstNieInTuer_GROB for 5
check gleichesErgebnisInFreinUndGrob for 5
check verfeinerungGrobUndFein for 5
check nurBewohnerKannTuerOeffnen for 5
check esBefindetSichImmerNurEinePersonInTuer for 5
check raumStrukturBleibtGleich for 5
check tuerStrukturBleibtGleich for 5
check alleTuerenSindImmerOffen for 5
