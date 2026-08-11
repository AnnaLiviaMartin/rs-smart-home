# Modelspezifikation

Dieses Dokument beschreibt die fachliche Modellierung des Smart-Home-Systems unabhängig von der konkreten Alloy- oder Lean-Implementierung nach dem Event-B Vorgehen.

# Einführung der Spezifikation

Sämtliche Objekte und deren Beziehungen, die in den Feineren Modellen erst definiert werden, gelten auch bereits im Groben Modell. 

# Grobes Modell

## Objekte und Beziehungen
- Es gibt Orte, in denen sich Personen aufhalten können.
- Türen und Räume sind Orte
- Es gibt Räume, die sich in Garten und Zimmer aufteilen
- Alle Räume sind über Türen miteinander Verbunden
- Eine Person kann sich in genau einem Raum aufhalten
- Alle Personen befinden zunächst im Garten
- Ex existiert genau ein Garten
- Alle Nachbarschaftsbeziehungen der Räume und Türen sind symmetrisch
- Alle Räume haben Türen als Nachbarn und Türen haben nur Räume als Nachbarn
- Türen können offen oder geschlossen sein

## Logik
- Personen können in Räume wechseln, sofern die verbindende Tür geöffnet ist
- Beispiel : Raum -> Raum
_(Sofern es Personenstatus zulassen - muss später noch eingefügt werden)_

# Verfeinertes Modell 01 (Zutrittskontrolle)

## Logik 
- Eine Person muss, wenn sie in den Raum wechselt, sich zwischendurch in der Tür befinden, sofern diese geöffent ist.
- Beispiel : Raum -> Tür -> Raum


# Verfeinertes Modell 02 (Physische Umsetzung)

## Objekte und Beziehungen
- Jede Tür hat ein eigenes Authentifizierungsgerät 

Personen:
- es gibt zwei Personentypen:
- Bewohner (können Türen aufschließen)
- Gäste (können keine Türen aufschließen)

## Logik
- Personen melden sich über Tür beim Authentifizierungsgerät an.
- Authentifizierungsgerät erkennt Bewohner und authentifiziert diese
- mit der Authentifizierung öffnet sich die Tür
- Gäste können nicht authentifiziert werden
- Authentifizierung schließt niemals Türen, sondern öffnet diese nur
- wenn Türen geschlossen, sind ist authentifizierung nötig
- geöffnete Türen fallen irgendwann wieder zu

## Szenarien:
**Tür geschlossen**
Gast -> auth -> x
Bewohner -> auth -> Tür -> Raum

**Tür offen**
Gast -> auth -> Tür -> Raum
Bewohner -> auth -> Tür -> Raum

# Verfeinerungsschritt 03

## Objekte und Beziehungen
- Es gibt einen Alarmraum 17
- Es gibt einen Herrn Weitz
- Herr Weitz ist ein Bewohner

## Logik
Alarm geht an wenn: 
- Jemand ohne Herrn Weitz in Raum 17 ist.