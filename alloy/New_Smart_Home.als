//  bitte alte Dateien löschen + thm-Datei für Ansehen bereitstellen 
// insgesamt fände ich es eine gute Idee mit den Überschriften das einheitlich zu machen, also alle gleiche Art und Beschreibung was die machen (so wie bei ###### axiome ), sodass man eine übersicht durch die dateistruktur selbst schon hat
// bitte ebenfalls alles englische auf deutsch machen
// und code löschen, der nicht mehr benötigt wird bzw. erklären warum er auskommentiert ist

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
	one nachbarn //Garten soll nur einen Zugang zum Haus haben
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

fact personKannNurDurchOffeneTürGehen {
	always all t: TUER, p: PERSON | p in t.personenImOrtGrob implies t.offen = True
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
		((betreteTuer[p, r1, t] and StutterSchritt_2[t]) or 
		(verlasseTuer[p, r2, t] and schrittGrob[p, r1, r2])) and 
		vorbedingungenMoveFein[r1, r2, t]
}

//#################### Zustandsübergänge / Ereignisse des Feinen Modells mit Autorisierung

pred schrittSehrFein {
	some p: PERSON, t: TUER |
		(oeffneTuer[p, t] and StutterSchritt_1[t]) or (schrittFein and tuerBleibtOffenOderFaelltZu)	
}

pred oeffneTuer [p: PERSON, tuer: TUER] {
	//pre
	p in BEWOHNER
	tuer in p.~personenImOrtFein.nachbarn //Tür muss nachbar zum Raum sein, in dem die person sich aufhält
	tuer.offen = False

	//post
	tuer.offen' = True
}

pred tuerBleibtOffenOderFaelltZu {
	all t: TUER | t.offen = False implies t.offen' = False 
}

fact show {
	init
	always schrittSehrFein 
}

//run show for exactly 2 PERSON, 1 GAST, 1 BEWOHNER, exactly 1 GARTEN, exactly 3 TUER, exactly 4 RAUM
// bitte nur ein run show von beidem oder erklären warum beide nötig sind
//run show

//################ Stutter ######################

pred StutterSchritt_1 [tuer: TUER] {
	all o: ORT | o.personenImOrtFein' = o.personenImOrtFein
	all o: ORT | o.personenImOrtGrob' = o.personenImOrtGrob
	all t: TUER - tuer | t.offen' = t.offen
}

pred StutterSchritt_2 [tuer: TUER]{
	all o: ORT | o.personenImOrtGrob' = o.personenImOrtGrob
	all t: TUER - tuer | t.offen' = t.offen
}

//################ Tests ######################

assert personNurInEinemOrt {
	always all p: PERSON |
		#(p.~personenImOrtFein) = 1
}

assert geschlosseneTuerIstLeer {
	always all t: TUER |
		t.offen = False implies no t.personenImOrtFein
}

assert bewegungDurchOffeneTuer {
	always all p: PERSON, t: TUER |
		p in t.personenImOrtFein implies t.offen = True
}

assert keineTeleportation_GROB {
	always all p: PERSON, von, nach: ORT | 
		(p in von.personenImOrtGrob and 
		p in nach.personenImOrtGrob' implies 
		(nach in von.nachbarn.nachbarn)) 
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

assert gleichesErgebnisInFreinUndGrob{
	always all p: PERSON, von: ORT |
		(p in von.personenImOrtGrob and p in von.personenImOrtFein) implies 
		(p in von.personenImOrtGrob' and p in von.personenImOrtFein') or 
		(p in von.personenImOrtGrob' and p in von.nachbarn.personenImOrtFein') or 
		(p in von.nachbarn.nachbarn.personenImOrtGrob' and p in von.nachbarn.nachbarn.personenImOrtFein')
}

assert verfeinerungKorrekt { // eventuell entfernen wenn andere assert funktioniert
	always all p: PERSON, r1, r2: RAUM | //Hier gabe es die verbesserung, dass es nur einen Garten geben darf, da dies dre Anfangsraum für alle ist, die Personen aber auf diese zwei gärten initial unglecih aufgeteilt waren.
		(p in r1.personenImOrtFein and p in r2.personenImOrtFein')
		implies (p in r1.personenImOrtGrob' and p in r2.personenImOrtGrob')
}

assert verfeinerungGrobUndFein {
	always all p: PERSON, r: RAUM |
		p in r.personenImOrtFein implies p in r.personenImOrtGrob
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

assert alleTuerenSindImmerOffen {
	always all t: TUER | t.offen = True
}

assert tuerIstGeschlossenBisBewohnerSieOeffnet { //evt was mit unitl ausprobieren

}

check personNurInEinemOrt for 5
check geschlosseneTuerIstLeer for 5 // Bruahct man das, wenn es bereits als axiom definiert ist?
check bewegungDurchOffeneTuer for 5
check keineTeleportation_GROB for 5
check personenImGrobmodellNurInRaeumen for 5
check keineTeleportation_FEIN for 5
check personIstNieInTuer_GROB for 5
check gleichesErgebnisInFreinUndGrob for 5
check verfeinerungGrobUndFein for 5
check nurBewohnerKannTuerOeffnen for 5
check raumStrukturBleibtGleich for 5
check tuerStrukturBleibtGleich for 5
check alleTuerenSindImmerOffen for 5

// ToDo : Checken, warum kein newConfic möglich ist ; Türen gehen manchmal automatisch wieder auf ohne autentifizierung ; PersonenGrob können noch in den Türen Spawnen

//Eigenschaften, die nicht als axiome gelten haben wir über Frame Vorgänge gehandelt, da diese nicht als natürliche Gesetze gelten, beispielsweise das eine PersonGrob nicht in einer Tür stehen kann.
//Problem: PersonGrob kann noch in Tür spawnen --> Frame Conditions überprüfen und code aufräumen
