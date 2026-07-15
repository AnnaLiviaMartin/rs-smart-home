# Smart Home Model Specification

## Ziel

Dieses Dokument beschreibt die fachliche Modellierung des Smart-Home-Systems unabhängig von der konkreten Alloy- oder Lean-Implementierung nach dem Event-B Vorgehen.

# 1. Anwesenheitserkennung & Zutrittskontrolle
TODO: 

Bis 01.07
- Diagramme mit Mermaid hinzufügen: UML-Diagramme, Entity-Relationship-Modell (Livia)
- Allergröbstes Modell in Alloy (Verena)
- Allergröbstes Modell in Lean (David)
- Karte malen (David)

Bis 08.07
- Alloy bis zum Feinen Modell ohne Alarmzustand (Livia, Verena check)
- Lean bis zum gröbsten Modell, ansonsten schauen wie weit man kommt (Verena)
- Präsentation und UML für alles (David)
- Mathematische Spezifikation festhalten (David)

Präsi - 30 Minuten
Pyramidales erzählen -> Erst das Ergebnis zeigen, dann die Theorie dahinter, damit man als Zuhörer von Informationen von anfang an einordnen kann
Demo: alloy und lean -> motivation -> theorie
Alloy ergebnisse mit screenshots zeigen
Lageplan praktisch für das Verständnis der Zuhörenden
Thematisch nach Spezifikation strukturieren, erst Grundstruktur anschließend Verfeinerung

Graphentheorie ist in Mathlib definiert? Generell schauen nach einer Graphenbibiliothek

Bis 12.07: 
- Spezifikation umbauen (Verena)
- Lean grobes modell (Livia)

Beweisen, dass grobe und Feine Modelle zusammenarbeiten in Alloy
Wir können in den ersten Zwei spezifikationsschritten die Objekte definieren und ab dem dritten schritt die Constraints. Ab dann können wir mit Event-B weiterdefinieren und Zusammenspiel von groben und feinem modell beweisen.

Bis 22.07:
- Lean (Livia, David)
- Alloy Verfeinerte Modelle mit beweisen (Verena)


# Einführung der Spezifikation
Sämtliche Objekte und deren Beziehungen, die in den Feineren Modellen erst definiert werden, gelten auch bereits im Groben Modell. 

# Grobes Modell

## Objekte und Beziehungen
- Ex gibt Orte, in denen sich Personen aufhalten können.
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

## Idee für später:

- wenn eine Person die Tür über das Authentifizierungsgerät öffnet, könnte durch die offene tür eine weitere Person den Raum betreten
- Dazu müsste gleichzeitige Bewegung von Personen möglich sein.

## Verworfen:

- Person wechselt zwischen Räumen:
    1. Person muss sich am Authentifizierungsgerät anmelden
    2. Authentifizierungsgerät muss Eintritt gewähren
    3. Authentifizierungsgerät muss Person eintragen (sofern sie durchgeht?)

- Person wechselt zwischen Räumen:
    1. Nach gewährung des Eintritts (Vereinfachung 01.2) anmelden
    2. Authentifizierungsgerät entsperrt Tür
    3. Tür öffnen
    4. Person wechselt Raum
    5. Tür schließen
    3. Authentifizierungsgerät muss Person eintragen (sofern sie durchgegangen ist?)
    6. Tür verriegeln