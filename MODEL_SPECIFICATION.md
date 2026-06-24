# Smart Home Model Specification

## Ziel

Dieses Dokument beschreibt die fachliche Modellierung des Smart-Home-Systems unabhängig von der konkreten Alloy- oder Lean-Implementierung nach dem Event-B Vorgehen.

# 1. Anwesenheitserkennung & Zutrittskontrolle
TODO: Diagramme mit Mermaid hinzufügen, UML-Diagramme, Entity-Relationship-Modell

## Gröbstes Modell

- Es gibt Räume
- Es gibt Personen
- Eine Person kann nur in einem Raum zu Zeitpunkt T sein
- Personen können zwischen Räumen hin und her wechseln
- Raumwechsel von Personen sind nur in benachbarten Räumen möglich

## Grobes Modell

- Räume können von Personen betreten werden
- Eine Person kann bis zu X Räume besitzen
- Ein Raum kann nur von Y* Personen (auch von keiner Person) besessen werden
- Ein Raum kann maximal Z* Personen fassen

z.B. Funktion: Person ist in Raum A und geht in Raum B. Sie wird dann aus Raum A entfernt und Raum B bekommt +1 Person.

### Feineres Modell

- Eine Person kann ein Gast sein
- Ein Bewohner ist eine Person die sowohl einen Raum besitzt als auch andere Räume besuchen kann
- Es gibt Räume in die keine Gäste können
- Es gibt Räume die Gäste nur mit Besitzer betreten können

### Alarm Modell

- Es gibt einen Normalzustand, in diesem gelten alle Regeln. Für den Alarmfall gelten spezielle Regeln.
- ...


# 2. Zugriffskontrolle

...