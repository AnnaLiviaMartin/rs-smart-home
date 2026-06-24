# Smart Home Verification with Alloy 6 and Lean

Dieses Projekt untersucht die formale Modellierung und Verifikation eines Smart-Home-Systems mit Fokus auf:

- Anwesenheitserkennung
- Zutritts- und Zugriffskontrolle
- Wetter- und Umweltsensorik

Zur Modellierung und Analyse werden **Alloy 6** und **Lean 4** verwendet.

## Ziele

Das Smart Home soll folgende Aspekte berücksichtigen:

### Schwerpunkt 1: Anwesenheitserkennung & Zutrittskontrolle

- Raumbelegung verfolgen
- Maximale Personenzahl in Räumen
- Automatische Besucherzählung
- Alarm, wenn sich Personen in gesperrten Bereichen befinden

- Notfallmodus: Bei Feuer werden alle Türen entriegelt, Bei Einbruch werden bestimmte Türen verriegelt
- Mehrstufige Authentifizierung: Raum nur mit Karte + PIN zugänglich
- Temporäre Berechtigungen: Gastzugang für 24 Stunden

### Schwerpunkt 2: Wetter- und Umweltsensoren

- Regen → Dachfenster schließen
- Hohe Windstärke → Markise einfahren
- Hohe Temperatur → Rollläden schließen
- Schlechte Luftqualität → Lüftung aktivieren

## Projektstruktur

```text
project/
│
├── README.md
├── MODEL_SPECIFICATION.md
│
├── alloy/
│   ├── smart_home.als
│
├── lean/
│   ├── SmartHome.lean
│
└── docs/
    └── diagrams/
```

## Installation

## Alloy ausführen

Modell laden:

```text
alloy/smart_home.als
```

Analyse starten:

```alloy
run {}
```

oder

```alloy
check PropertyName
```

## Lean ausführen

Projekt bauen:

```bash
lake build
```

Einzelne Datei prüfen:

```bash
lean SmartHome.lean
```

## Modellbeschreibung

Die fachliche Beschreibung des Smart-Home-Modells befindet sich in:

[MODEL_SPECIFICATION.md](MODEL_SPECIFICATION.md)

Dort werden definiert:

- Entitäten
- Zustände
- Beziehungen
- Sicherheitsregeln
- Sensorregeln
- Zu verifizierende Eigenschaften