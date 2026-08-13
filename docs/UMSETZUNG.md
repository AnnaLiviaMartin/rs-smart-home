# Umsetzungsentscheidungen

Dieses Dokument beschreibt die konkreten Modellierungs- und Implementierungsentscheidungen für das Smart-Home-System.

Die fachlichen Anforderungen sind in der [Modellspezifikation](./Modellspezifikation.md) beschrieben. Dieses Dokument erklärt, wie diese Anforderungen in Alloy und Lean als Modell umgesetzt und bewiesen wurden.

## Ziel der Umsetzung

Ziel der Umsetzung ist es, die drei fachlichen Modelle formal abzubilden:

1. das grobe Modell mit direkten Bewegungen zwischen Räumen,
2. das erste verfeinerte Modell mit dem Aufenthalt in einer Tür, während des Raumwechsels,
3. das zweite verfeinerte Modell mit einer Authentifizierung für das Öffnen der Tür.

Alloy wird verwendet, um mögliche Zustände und Abläufe automatisch zu untersuchen. Lean wird verwendet, um ausgewählte Eigenschaften formal zu beweisen.

## Verwendete Werkzeuge

### Alloy

Alloy wird für die automatische Zustands- und Ablaufanalyse verwendet.

Mit Alloy werden insbesondere folgende Eigenschaften untersucht:

- Jede Person befindet sich genau an einem Ort.
- Jede Tür verbindet genau zwei Räume.
- Bewegungen sind nur über verbundene Räume möglich.
- Geschlossene Türen können nicht ohne Authentifizierung passiert werden.
- Ereignisse verletzen keine Systemgarantien.

### Umsetzung des Groben Modells

Um erste Bewegungsabläufe von Personen zwischen Räumen modellieren zu können, jedoch bereits den Grundaufbau des Gebäudes für die nächsten Verfeinerungsschritte vorzubereiten, haben wir zunächst Personen und unterschiedliche Orte definiert. 

Dabei haben wir Orte in Räume und Gärten aufgeteilt. Eine Person kann sich in einem Ort aufhalten.

![Grobes Modell mit Bernd in Raum A](pictures/Alloy_Raumplan_Grob_Bernd.png)

Personen können nun zwischen benachbarten Räumen wechseln. Dafür enthält jeder Raum eine Liste aus Nachbarräumen. Wichtig ist, dass Nachbarräume Symmetrisch sind, weshalb wir dies als fact in Alloy für unsere Raumstruktur festgelegt haben (siehe Alloymodell: fact alleNachbarnSindSymmerisch).

Die Bewegung wurde definiert als das Entfernen der Person aus Raum A und das Hinzufügen dieser in den benachbarten Raum B (siehe Alloymodell: pred move).

![Grobes Modell mit Bernd in Raum B](pictures/Alloy_Raumplan_Grob_Bernd_B.png)

### Umsetzung des Feinen Modells

Im Feinen Modell wurden nun Türen zwischen den Räumen modelliert, durch die die Personen gehen müssen, um in einen benachbarten Raum zu wechseln. Der Wechsel in den benachbarten Raum teilt sich nun in zwei Zwischenschritte auf: 

1. Die Person betritt die Tür
2. Die Person verlässt die Tür

![Feines Modell mit Zwischenschritt](pictures/Alloy_Raumplan_Fein_Bernd_Tuer.svg)

Eine Eingeführte Vorraussetzung ist, dass die Tür, durch die eine Person gehen möchte, geöffnet sein muss. Dies haben wir als pre-Bedingung festgehalten(siehe Alloymodell: pred betreteTuer).

Da an dieser Stelle für einen einzelnen Schritt im Groben Modell zwei Schritte im Feinen Modell notwendig sind. Ist die einführung eines ersten Stutter-Vorgangs im Groben Modell wichtig.

Ziel ist, dass das Ergebnis des Feinen Modells auch im Ergebnis des Groben Modells vorhanden sein soll. Zwischenschritte des Feinen Modells sind entsprechend als Blackbox im Groben Modell zu betrachten. 

|  | Schritt 1 | Schritt 2 |
|----------|----------|----------|
| Grob   | Stutter   | betreteRaum   |
| Fein   | betreteTuer   | verlasseTuer   |

In diesem Stutter-Vorgang ist festgelegt, dass sich die Person im Groben Modell nicht bewegt. Dies wurde mit einer Frame-Condition ermöglicht, die definiert, dass sämtliche Personen in dem Modell in ihrem aktuellen Raum bleiben.

Ziel war es, wenn sich eine Person im Feinen Modell in Raum A, befindet, dass dies auch für das Grobe Modell gilt.

Wenn die Person allerdings die Tür verlässt und Raum B betritt, soll das für das Grobe Modell ebenfalls gelten.

Wenn die Person im Feinen Modell in der Tür steht, ist das aus Sicht des Groben Modells betrachtet, eine Blackbox:

![Modell mit Zwischenschritt der ersten Verfeinerung](pictures/Alloy_Raumplan_Grob_Fein_Tuer.svg)

### Umsetzung der Authentifizierung

Im zweiten Verfeinerungsschritt, wurde nun die Möglichkeit eingeführt, dass Bewohner sich authentifizieren müssen, um eine Tür zwischen benachbarten Räumen öffnen zu können. Wenn die Tür geöffnet wurde, besteht für Personen wieder die Möglichkeit eines Raumwechsels. 

Da sich nur Bewohner Authentifizieren können, ist es nun notwendig, Personen in Bewohner und Gäste aufzuteilen. 

Zusätzlich zum Betreten der Tür ist also ein weiterer Zwischenschritt nötig:

|  | Schritt 1 | Schritt 2 | Schritt 3 |
|----------|----------|----------|----------|
| Grob   | Stutter   | Stutter   | betreteRaum |
| Fein   | Stutter   | betreteTuer   | verlasseTuer |
| Auth   | Tuer oeffnen   | betreteTuer   | verlasseTuer |

Da es nun meherere Personen gibt, die in dem Modell exisiteren, ist es nun wichtig, dass die Personen, die keine Räume wechseln, in ihren aktuellen Räumen bleiben. Dies wird durch Frame-Conditions ermöglicht, die in den einzelnen Stutter-Vorgängen gesetzt sind. Stutter-Vorgänge werden verwendet, um Alloy mit Einschränkungen hinsichtlich der Modellgenerierung an Verhalten außerhalb der definierten Logik zu hindern.

Stutter_Schritt_1: Personen, 



Frame Conditions mit stutter, damit personen nicht spawnen

### Umsetzung der Gebäude Struktur mit mehreren Räumen



### Lean

Lean wird für mathematische Beweise verwendet.

In Lean werden insbesondere folgende Eigenschaften betrachtet:

- Die Invarianten bleiben nach einer Bewegung erhalten.
- Eine Person befindet sich nach einer Bewegung weiterhin genau an einem Ort.
- Eine Tür verbindet weiterhin genau zwei Räume.
- Eine fehlgeschlagene Authentifizierung verändert den Zustand nicht.
- Die Verfeinerung liefert dasselbe fachliche Ergebnis wie das grobe Modell.

## Alloy-Modelle

Dieses Kapitel beschreibt, wie Alloy verwendet wird.

### Modellbestandteile

| Alloy-Konstrukt | Bedeutung |
| :--- | :--- |
| **sig** | Menge beziehungsweise Typ von Objekten |
| **extends** | Spezialisierung einer Menge |
| **fact** | Regel, die immer gelten muss |
| **pred** | Wiederverwendbare Operation oder Bedingung |
| **assert** | Zu überprüfende Behauptung |
| **check** | Prüfung einer Behauptung |
| **run** | Suche nach einem gültigen Beispiel |
| **always** | Eigenschaft gilt in allen Zuständen |

### Abbildung der Objekte

### Vereinfachungen und Grenzen

## Lean-Modelle

Dieses Kapitel beschreibt, wie Lean verwendet wird.

### Abbildung der Objekte aus Alloy nach Lean

### Definition von Zuständen

### Definition von Übergängen

### Formulierung der Invarianten

### Beweis ausgewählter Eigenschaften

## Unterschiede zwischen Alloy und Lean**
*Vergleichstabelle*

| Alloy | Lean |
| :--- | :--- |
| Suche nach Gegenbeispielen | Konstruktion formaler Beweise |
| Zustände und Relationen | Typen, Funktionen und Sätze |
| `check` | `theorem` beziehungsweise `lemma` |
| begrenzter Suchraum | grundsätzlich allgemeiner Beweis |
| Modellprüfung | interaktives beziehungsweise automatisiertes Beweisen |