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

Präsi - 20 Minuten
Pyramidales erzählen -> Erst das Ergebnis zeigen, dann die Theorie dahinter, damit man als Zuhörer von Informationen von anfang an einordnen kann
Demo: alloy und lean -> motivation -> theorie
Alloy ergebnisse mit screenshots zeigen
Lageplan praktisch für das Verständnis der Zuhörenden
Thematisch nach Spezifikation strukturieren, erst Grundstruktur anschließend Verfeinerung

Graphentheorie ist in Mathlib definiert? Generell schauen nach einer Graphenbibiliothek


### Allergröbstes Modell

- Es gibt Räume.
- Es gibt mindestens zwei Räume.
- Räume haben Nachbarräume.
- Symmetrie: Räume haben sich gegenseitig als Nachbarn. 
- Räume haben sich selbst nicht zum Nachbarn.
- Räume sind eindeutig identifizierbar.
- Räume sind statisch. Sie bleiben an ihrer Raum-Topologie-Stelle.
- Jeder Raum ist durch das betreten weiterer Nachbarräume irgendwann erreichbar (alle Räume sind in einem Gebäude).

Hier ist das zugehörige [Klassendiagramm](docs/diagrams/allergroebstes-modell.plantuml) zum besseren Verständnis ansehbar.

## Gröbstes Modell

- Es gibt Personen.
- Eine Person kann nur in einem Raum zu Zeitpunkt T sein.
- Personen können zwischen Räumen hin und her wechseln (Räume können von Personen betreten werden).
- Raumwechsel von Personen sind nur in benachbarten Räumen möglich.

## Grobes Modell

- Ein Raum kann nur von Y* Personen besessen werden.
- Eine Person kann bis zu X* Räume besitzen.
- Ein Raum kann maximal Z* Personen fassen.

z.B. Funktion: Person ist in Raum A und geht in Raum B. Sie wird dann aus Raum A entfernt und Raum B bekommt +1 Person.

### Feineres Modell

- Eine Person kann entweder ein Gast oder ein Bewohner sein.
- Ein Bewohner ist eine Person, die mindestens einen Raum besitzt.
- Alle Personen haben immer in freie Räume zutritt.
- Begleiträume dürfen von Gästen nur betreten werden, wenn ein Bewohner in diesem Raum ist.
- Ein Privatraum hat mindestens einen Besitzer, der Bewohner ist
- Privaträume dürfen nur vom jeweiligen Bewohner/Besitzer des Raumes betreten werden.

### Außnahmenzustands-Modell

- Es gibt verschiedene Außnahmezustände.
- Tritt der Zustand-Alarmzustand ein, dürfen Personen den Raum in dem sie sich gerade befinden, nicht mehr verlassen.
- Räume bestehen aus dichten Räumen (mit Dach) und Gärten.
- Jeder Garten hat mindestens einen dichten Raum als Nachbar.
- Tritt der Zustand-Regen ein, müssen alle Personen in einem dichten Raum sein. Gärten müssen verlassen werden.
(- Tritt der Zustand-Feuer ein, tritt das Gegenteil von Zustand-Regen ein)

# Anmerkungen zur Notation

- X* := X kann Werte zwischen 0 und unendlich annehmen