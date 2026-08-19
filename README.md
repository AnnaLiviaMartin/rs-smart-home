# Formale Spezifikation und Verifikation eines Zutritts- und Bewegungssystems mit Alloy und Lean

Dieses Projekt beschreibt und überprüft ein Smart-Home-System zur Anwesenheitserkennung und Zutrittskontrolle.

Im Mittelpunkt stehen Personen, Räume, Türen und Authentifizierungseinrichtungen. Personen können sich zwischen Räumen bewegen. Der Zugang zu bestimmten Räumen wird über Türen kontrolliert.

Für die Modellierung und Analyse werden folgende Werkzeuge verwendet:

- **Alloy 6** zur Modellprüfung und zur Suche nach Gegenbeispielen
- **Lean 4** zur formalen Überprüfung und zum Beweisen ausgewählter Eigenschaften

## Dokumentation

Die Dokumentation ist auf mehrere Dateien verteilt. Diese README.md dient als Einstiegspunkt und gibt einen Überblick über das Projekt.

### Fachliche Idee und Motivation

Die Motivation, die fachliche Problemstellung und die Herleitung des Modells befinden sich in der [Dokumentation.md](docs/DOKUMENTATION.md)

Dieses Dokument beschreibt unter anderem:

- das zugrunde liegende Problem,
- die beteiligten Personen und Orte,
- die Bewegungsmöglichkeiten,
- die Bedeutung der Türen,
- die Unterscheidung zwischen grobem und feinem Modell.

### Fachliche Spezifikation

Die fachlichen Regeln und Bedingungen des Systems befinden sich in [Model_Spezifikation.md](docs/Model_Spezifikation.md)

Dort wird das Modell zunächst unabhängig von Alloy und Lean beschrieben.

Behandelt werden unter anderem:

- Systemobjekte,
- Zustände,
- Bewegungsregeln,
- Türzustände,
- Authentifizierung,
- Invarianten,
- erwartete Systemabläufe.

### Umsetzungsentscheidungen

Die Beschreibung der konkreten Modellierungs- und Implementierungsentscheidungen befindet sich in [Dokumentation.md](docs/DOKUMENTATION.md)

Dort wird erklärt, wie die fachlichen Anforderungen in Alloy und Lean umgesetzt wurden.

## Projektstruktur

Das Projekt ist wie folgt aufgebaut:

```text
project/
│
├── README.md
│
├── docs/
│   ├── Dokumentation.md
│   ├── Model_Spezifikation.md
│   ├── Umsetzung.md
│   └── diagrams/
│   └── pictures/
│
├── alloy/
│   ├── smart_home.als
│   └── smart_home.thm
│
├── LeanProjekt/
│   ├── LeanProjekt
│       ├── Main.lean
│       └── Beispiel.lean
```

### Verzeichnisse und Dateien

Die Umsetzungen befinden sich in den folgenden Verzeichnissen:

- [Alloy-Modell](alloy/)
- [Lean-Modell](LeanProjekt/LeanProjekt)

Das Alloy-Modell dient insbesondere dazu, mögliche Modellinstanzen zu erzeugen und Eigenschaften innerhalb eines begrenzten Suchraums zu überprüfen.

Lean wird verwendet, um ausgewählte Eigenschaften formal zu formulieren und zu beweisen.

Weitere wichtige Dateien, sind folgend aufgelistet:

| Pfad | Beschreibung |
| :--- | :--- |
| `docs/` | Ausführliche Projektdokumentation |
| `alloy/` | Alloy-Modell und zugehörige Darstellungsdateien |
| `smart_home.als` | Formale Alloy-Spezifikation |
| `Main.lean` | Formale Lean-Spezifikation |
| `Beispiel.lean` | Beispiele für die Lean-Spezifikation |

## Alloy ausführen

### Voraussetzungen

Für die Ausführung wird Alloy 6 benötigt.

### Ausführung

Modell laden:

```text
alloy/smart_home.als
```

Analyse starten:

```alloy
run {}
```

oder Eigenschaft überprüfen:

```alloy
check PropertyName
```

Die Style-Datei für's Ansehen des Alloy-Modells, findet sich unter [Styling](/alloy/smart_home.thm)

## Lean ausführen

### Voraussetzungen

Für die Ausführung wird Lean 4 mit Lake benötigt.

### Ausführung

Projekt bauen:

```bash
lake build
```

Einzelne Datei prüfen:

```bash
lean Main.lean
```

Lean ist in zwei Dateien aufgesplittet. Die erste Datei [Main.lean](/LeanProjekt/LeanProjekt/Main.lean) stellt die Beweise bereit. Die zweite Datei  [Beispiel.lean](/LeanProjekt/LeanProjekt/Beispiel.lean) stellt ein Beispiel zur Verfügung.

## Bild-Quellen

Bernd das Brot: https://erfurt-mitte.de/blogs/erfurt-mitte-blog/bernd-das-brot-merchandise-im-onlineshop-kultiges-kultbrot-fuer-fans

Sandmännchen: https://www.gmx.ch/magazine/unterhaltung/tv-shows/24-zentimeter-gross-unermuedlich-sandmann-55-30229448

Geschlossenes Schloss: https://www.strzmetal.com/pid18438420/Customized-Safety-Pad-Lock-Brass-Padlock-for-Global-Brands-OEM-ODM-Wholesale.htm

Geöffnetes Schloss: https://www.couhome.com/2024/04/door-lock-types.html

Alle anderen Diagramme/Bilder sind durch uns erstellt worden.