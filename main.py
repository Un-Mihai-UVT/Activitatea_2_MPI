import time
import random
from copy import deepcopy

limita_clauze_rezolutie = 1000000 #Limita aleasa arbitrar consuma foarte multe resurse (memorie si timp) daca este mai mare
limita_clauze_dp = 1000000 #La fel si pentru dp


# --- Parsor DIMACS ---
def parseaza_dimacs(cale_fisier):
    """Parseaza un fisier in format DIMACS."""
    clauze = []
    numar_variabile = 0
    numar_clauze_asteptat = 0
    try:
        with open(cale_fisier, 'r') as f:
            for linie in f:
                linie = linie.strip()
                if not linie or linie.startswith('c'):
                    continue
                if linie.startswith('p cnf'):
                    parti = linie.split()
                    if len(parti) != 4:
                        raise ValueError("Format invalid pentru linia 'p'")
                    numar_variabile = int(parti[2])
                    numar_clauze_asteptat = int(parti[3])
                else:
                    try:
                        literali = list(map(int, linie.split()))
                        if not literali or literali[-1] != 0:
                            if literali and literali[-1] != 0:
                                print(f"Avertisment: Linia de clauza nu se termina cu 0, se adauga implicit: {linie}")
                            elif not literali:
                                print(f"Avertisment: Se omite linia goala sau invalida: {linie}")
                                continue

                        continut_clauza = literali[:-1] if literali and literali[-1] == 0 else literali

                        if continut_clauza:
                            clauze.append(continut_clauza)
                        else:
                            print(
                                "Avertisment: Clauza goala '0' detectata in fisierul de intrare. Formula este UNSAT.")
                            clauze.append([])

                    except ValueError:
                        raise ValueError(f"Format invalid al literalilor in linia: {linie}")

            if numar_variabile == 0 and clauze:
                print("Avertisment: Linia 'p cnf' nu a fost gasita sau numar_variabile este 0.")
                toate_variabilele = set(abs(literal) for clauza in clauze for literal in clauza)
                numar_variabile = max(toate_variabilele) if toate_variabilele else 0
                print(f"Numar de variabile dedus: {numar_variabile}")

            if numar_clauze_asteptat > 0 and len(clauze) != numar_clauze_asteptat:
                print(
                    f"Avertisment: Se asteptau {numar_clauze_asteptat} clauze (conform liniei 'p'), dar s-au gasit {len(clauze)} clauze efective.")

            if numar_variabile > 0:
                for clauza in clauze:
                    for literal in clauza:
                        if abs(literal) > numar_variabile or literal == 0:
                            if literal == 0 and clauza:
                                raise ValueError(f"Literalul 0 gasit intr-o clauza non-goala: {clauza}")
                            elif abs(literal) > numar_variabile:
                                raise ValueError(
                                    f"Literal invalid {literal} pentru numar_variabile {numar_variabile} in clauza {clauza}")

            print(f"S-au parsat {len(clauze)} clauze cu {numar_variabile} variabile din {cale_fisier}")
            if any(not c for c in clauze):
                print("Nota: Formula contine initial o clauza goala -> UNSAT")
            return clauze, numar_variabile

    except FileNotFoundError:
        print(f"Eroare: Fisierul nu a fost gasit la {cale_fisier}")
        return None, 0
    except Exception as e:
        print(f"Eroare la parsarea fisierului DIMACS: {e}")
        import traceback
        traceback.print_exc()
        return None, 0


# --- Generator FNC (Forma Normala Conjunctiva) ---
def genereaza_fnc(numar_variabile, numar_clauze, k=3, asigura_satisfiabilitate=False):
    """Genereaza o formula k-FNC aleatorie."""
    if k > numar_variabile and numar_variabile > 0:
        raise ValueError("k (lungimea clauzei) nu poate fi mai mare decat numar_variabile")
    if k <= 0:
        raise ValueError("k (lungimea clauzei) trebuie sa fie pozitiv")

    clauze_set = set()

    atribuire_adevarata = None
    if asigura_satisfiabilitate:
        if numar_variabile == 0:
            print("Avertisment: Nu se poate asigura satisfiabilitatea pentru 0 variabile.")
        else:
            atribuire_adevarata = {v: random.choice([True, False]) for v in range(1, numar_variabile + 1)}
            print(f"Se asigura satisfiabilitatea cu o atribuire ascunsa.")

    variabile = list(range(1, numar_variabile + 1))
    incercari = 0
    max_incercari = numar_clauze * 100  # Limita de siguranta (arbitrar aleasa logic)

    while len(clauze_set) < numar_clauze and incercari < max_incercari:
        incercari += 1
        if not variabile:
            if len(clauze_set) < numar_clauze:
                print(f"Avertisment: Nu se pot genera {numar_clauze} clauze cu {numar_variabile} variabile si k={k}.")
                break
            else:
                continue

        variabile_alese = random.sample(variabile, min(k, len(variabile)))
        clauza_curenta = set()
        for variabila in variabile_alese:
            literal = variabila * random.choice([1, -1])
            clauza_curenta.add(literal)

        este_tautologie = False
        for literal in clauza_curenta:
            if -literal in clauza_curenta:
                este_tautologie = True
                break
        if este_tautologie:
            continue

        if asigura_satisfiabilitate and atribuire_adevarata:
            satisfacuta = False
            for literal in clauza_curenta:
                variabila = abs(literal)
                este_negat = literal < 0
                if (not este_negat and atribuire_adevarata.get(variabila, False)) or \
                        (este_negat and not atribuire_adevarata.get(variabila, True)):
                    satisfacuta = True
                    break
            if not satisfacuta:
                continue

        tuplu_clauza = frozenset(clauza_curenta)
        if tuplu_clauza not in clauze_set:
            clauze_set.add(tuplu_clauza)

    if incercari >= max_incercari:
        print(
            f"Avertisment: S-a atins numarul maxim de incercari ({max_incercari}) inainte de a genera {numar_clauze} clauze unice. S-au generat {len(clauze_set)}.")

    clauze_finale = [list(fs) for fs in clauze_set]
    print(f"S-au generat {len(clauze_finale)} clauze cu {numar_variabile} variabile (k={k}).")
    return clauze_finale, numar_variabile


# --- Algoritmul de Rezolutie ---
def rezolva(clauza1, clauza2):
    """Efectueaza pasul de rezolutie intre doua clauze."""
    rezolventi = []

    for literal1 in clauza1:
        if -literal1 in clauza2:
            set_clauza_noua = (set(clauza1) - {literal1}).union(set(clauza2) - {-literal1})

            este_tautologie = False
            for literal in set_clauza_noua:
                if -literal in set_clauza_noua:
                    este_tautologie = True
                    break

            if not este_tautologie:
                tuplu_rezolvent = tuple(
                    sorted(list(set_clauza_noua)))
                rezolventi.append(tuplu_rezolvent)

            break
    return rezolventi


def rezolva_prin_rezolutie(clauze_intrare, numar_variabile, timp_maxim):
    """Incearca sa demonstreze nesatisfiabilitatea folosind rezolutia."""
    timp_start = time.perf_counter()
    statistici_rezolutie = {'rezolutii': 0, 'clauze_generate': 0, 'clauza_goala_gasita': False, 'iteratii': 0,
                            'saturare_atinsa': False}

    if any(not c for c in clauze_intrare):
        statistici_rezolutie['clauza_goala_gasita'] = True
        return "UNSAT", None, statistici_rezolutie

    clauze_curente = set(tuple(sorted(c)) for c in clauze_intrare if c)
    numar_initial_clauze = len(clauze_curente)
    derivate_recent_in_runda = set(clauze_curente)

    iteratie = 0
    while True:
        iteratie += 1
        statistici_rezolutie['iteratii'] = iteratie

        if time.perf_counter() - timp_start > timp_maxim:
            statistici_rezolutie['clauze_generate'] = len(clauze_curente) - numar_initial_clauze
            return "TIMP_DEPASIT", None, statistici_rezolutie

        derivate_in_aceasta_iteratie = set()
        clauze_de_confruntat = list(clauze_curente)
        clauze_noi_de_procesat = list(derivate_recent_in_runda)

        if not clauze_noi_de_procesat:
            break

        perechi_procesate_iteratie_curenta = 0
        max_perechi_per_iteratie = 100000
        # Limita aleasa arbitrar, poate fi modificata insa nu ar face mare diferenta pe rezolutie ca oricum crapa repede

        for tuplu_clauza_noua in clauze_noi_de_procesat:
            if perechi_procesate_iteratie_curenta > max_perechi_per_iteratie: break
            lista_clauza_noua = list(tuplu_clauza_noua)

            for tuplu_clauza_existenta in clauze_de_confruntat:
                if perechi_procesate_iteratie_curenta > max_perechi_per_iteratie: break
                if tuplu_clauza_noua == tuplu_clauza_existenta: continue

                if perechi_procesate_iteratie_curenta % 5000 == 0 and time.perf_counter() - timp_start > timp_maxim:
                    statistici_rezolutie['clauze_generate'] = len(clauze_curente) - numar_initial_clauze
                    return "TIMP_DEPASIT", None, statistici_rezolutie

                lista_clauza_existenta = list(tuplu_clauza_existenta)
                rezolventi = rezolva(lista_clauza_noua, lista_clauza_existenta)
                statistici_rezolutie['rezolutii'] += 1
                perechi_procesate_iteratie_curenta += 1

                for tuplu_rez in rezolventi:
                    if not tuplu_rez:
                        statistici_rezolutie['clauza_goala_gasita'] = True
                        statistici_rezolutie['clauze_generate'] = len(
                            clauze_curente | derivate_in_aceasta_iteratie) - numar_initial_clauze
                        return "UNSAT", None, statistici_rezolutie

                    if tuplu_rez not in clauze_curente and tuplu_rez not in derivate_in_aceasta_iteratie:
                        derivate_in_aceasta_iteratie.add(tuplu_rez)

        if not derivate_in_aceasta_iteratie:
            statistici_rezolutie['saturare_atinsa'] = True
            statistici_rezolutie['clauze_generate'] = len(clauze_curente) - numar_initial_clauze
            return "NECUNOSCUT (Rezolutie saturata)", None, statistici_rezolutie

        derivate_recent_in_runda = derivate_in_aceasta_iteratie
        clauze_curente.update(derivate_in_aceasta_iteratie)

        limita_clauze = max(2 * numar_initial_clauze + 5000, limita_clauze_rezolutie)
        if len(clauze_curente) > limita_clauze:
            print(f"Avertisment: Setul de clauze al rezolutiei a depasit limita ({limita_clauze}). Oprire.")
            statistici_rezolutie['clauze_generate'] = len(clauze_curente) - numar_initial_clauze
            return "NECUNOSCUT (Explozie de clauze)", None, statistici_rezolutie


# --- Algoritmul Davis-Putnam (Original) ---
def dp_elimina_variabila(clauze, variabila_de_eliminat):
    """Elimina o variabila folosind rezolutia, conform algoritmului DP original."""
    clauze_cu_pozitiv = []
    clauze_cu_negativ = []
    alte_clauze = []

    for clauza in clauze:
        set_clauza = set(clauza)
        if variabila_de_eliminat in set_clauza:
            clauze_cu_pozitiv.append(clauza)
        elif -variabila_de_eliminat in set_clauza:
            clauze_cu_negativ.append(clauza)
        else:
            alte_clauze.append(clauza)

    if not clauze_cu_pozitiv or not clauze_cu_negativ:
        return alte_clauze + clauze_cu_pozitiv + clauze_cu_negativ, 0

    clauze_noi_din_rezolutie = set()
    rezolutii_efectuate = 0

    for clauza_poz in clauze_cu_pozitiv:
        for clauza_neg in clauze_cu_negativ:
            set_rezolvent = (set(clauza_poz) - {variabila_de_eliminat}).union(
                set(clauza_neg) - {-variabila_de_eliminat})

            este_tautologie = False
            for literal in set_rezolvent:
                if -literal in set_rezolvent:
                    este_tautologie = True
                    break

            if not set_rezolvent:
                return [[]], 1

            if not este_tautologie:
                clauze_noi_din_rezolutie.add(tuple(sorted(list(set_rezolvent))))

            rezolutii_efectuate += 1

    clauze_finale = alte_clauze + [list(c) for c in clauze_noi_din_rezolutie]
    return clauze_finale, rezolutii_efectuate


def rezolva_dp(clauze_intrare, numar_variabile, timp_maxim):
    """Incearca sa rezolve SAT folosind eliminarea variabilelor (Davis-Putnam original)."""
    timp_start = time.perf_counter()
    statistici_dp = {'variabile_eliminate': 0, 'rezolutii': 0, 'max_clauze': len(clauze_intrare)}

    if any(not c for c in clauze_intrare):
        return "UNSAT", None, statistici_dp

    clauze_curente = deepcopy(clauze_intrare)
    variabile = list(range(1, numar_variabile + 1))

    for index_var, variabila in enumerate(variabile):
        if time.perf_counter() - timp_start > timp_maxim:
            return "TIMP_DEPASIT", None, statistici_dp

        clauze_curente, numar_rezolutii = dp_elimina_variabila(clauze_curente, variabila)
        statistici_dp['rezolutii'] += numar_rezolutii
        statistici_dp['variabile_eliminate'] += 1
        statistici_dp['max_clauze'] = max(statistici_dp['max_clauze'], len(clauze_curente))

        if clauze_curente == [[]] or any(not c for c in clauze_curente):
            return "UNSAT", None, statistici_dp

        limita_clauze = max(2 * len(clauze_intrare) + 5000, limita_clauze_dp)
        if len(clauze_curente) > limita_clauze:
            print(
                f"Avertisment: Setul de clauze DP a crescut prea mult ({len(clauze_curente)} clauze, limita {limita_clauze}). Oprire.")
            return "NECUNOSCUT (Explozie de clauze)", None, statistici_dp

    if not clauze_curente:
        return "SAT", None, statistici_dp
    elif any(not c for c in clauze_curente):
        return "UNSAT", None, statistici_dp
    else:
        print(f"Avertisment: DP s-a incheiat cu clauze non-goale ramase: {clauze_curente}. Se presupune SAT.")
        return "SAT", None, statistici_dp


# --- Algoritmul DPLL ---
class StatisticiDpll:
    """Clasa simpla pentru a stoca statistici DPLL."""

    def __init__(self):
        self.decizii = 0
        self.propagari_unitare = 0
        self.reveniri = 0  # Backtracks


def simplifica_clauzele(clauze, atribuire):
    """Simplifica setul de clauze pe baza atribuirii partiale curente."""
    clauze_simplificate = []
    conflict = False
    for clauza in clauze:
        clauza_noua = []
        satisfacuta_prin_atribuire = False

        for literal in clauza:
            variabila = abs(literal)
            este_negat = literal < 0

            if variabila in atribuire:
                valoare_atribuita = atribuire[variabila]
                if (not este_negat and valoare_atribuita is True) or \
                        (este_negat and valoare_atribuita is False):
                    satisfacuta_prin_atribuire = True
                    break
            else:
                clauza_noua.append(literal)

        if not satisfacuta_prin_atribuire:
            if not clauza_noua:
                return [], True
            clauze_simplificate.append(clauza_noua)

    return clauze_simplificate, False


def propaga_unitar(clauze, atribuire, statistici):
    """Efectueaza propagarea unitara (Boolean Constraint Propagation - BCP)."""
    while True:
        literali_unitari_gasiti_iteratie = []

        for clauza in clauze:
            literal_neatribuit = None
            numar_neatribuiti = 0
            este_satisfacuta = False
            este_falsificata = True

            for literal in clauza:
                variabila = abs(literal)
                este_negat = literal < 0

                if variabila in atribuire:
                    valoare_atribuita = atribuire[variabila]
                    if (not este_negat and valoare_atribuita is True) or \
                            (este_negat and valoare_atribuita is False):
                        este_satisfacuta = True
                        break
                else:
                    numar_neatribuiti += 1
                    literal_neatribuit = literal
                    este_falsificata = False

            if este_satisfacuta:
                continue

            if not este_falsificata and numar_neatribuiti == 1:
                literali_unitari_gasiti_iteratie.append(literal_neatribuit)
            elif este_falsificata and numar_neatribuiti == 0:
                return [], True

        if not literali_unitari_gasiti_iteratie:
            break

        atribuire_facuta_iteratie = False
        for literal in literali_unitari_gasiti_iteratie:
            variabila = abs(literal)
            valoare = literal > 0

            if variabila not in atribuire:
                atribuire[variabila] = valoare
                statistici.propagari_unitare += 1
                atribuire_facuta_iteratie = True
            elif atribuire[variabila] != valoare:
                return [], True

        if not atribuire_facuta_iteratie:
            break

        clauze, conflict = simplifica_clauzele(clauze, atribuire)
        if conflict:
            return clauze, True

    return clauze, False


def atribuie_literal_pur(clauze, atribuire, statistici):
    """Gaseste si atribuie literali puri (apar doar cu o singura polaritate)."""
    polaritate_literal = {}
    variabile_neatribuite_in_clauze = set()

    for clauza in clauze:
        for literal in clauza:
            variabila = abs(literal)
            if variabila not in atribuire:
                variabile_neatribuite_in_clauze.add(variabila)
                polaritate = 1 if literal > 0 else -1

                polaritate_curenta = polaritate_literal.get(variabila)
                if polaritate_curenta is None:
                    polaritate_literal[variabila] = polaritate
                elif polaritate_curenta != 0 and polaritate_curenta != polaritate:
                    polaritate_literal[variabila] = 0

    atribuit_pur = False
    atribuite_in_pas = {}
    for variabila in variabile_neatribuite_in_clauze:
        polaritate = polaritate_literal.get(variabila)
        if polaritate == 1:
            if variabila not in atribuire:
                atribuire[variabila] = True
                atribuite_in_pas[variabila] = True
                atribuit_pur = True
        elif polaritate == -1:
            if variabila not in atribuire:
                atribuire[variabila] = False
                atribuite_in_pas[variabila] = False
                atribuit_pur = True

    if atribuit_pur:
        clauze, conflict = simplifica_clauzele(clauze, atribuite_in_pas)
        if conflict:
            print("Avertisment: Conflict detectat in timpul simplificarii literalilor puri!")
            return clauze, True

    return clauze, False


def selecteaza_variabila_ramificare(atribuire, numar_variabile):
    """Selecteaza urmatoarea variabila neatribuita pentru ramificare."""
    for variabila in range(1, numar_variabile + 1):
        if variabila not in atribuire:
            return variabila
    return None


def dpll_recursiv(clauze, atribuire, numar_variabile, statistici, timp_start, timp_maxim):
    """Functia recursiva a solver-ului DPLL."""
    timp_curent = time.perf_counter()
    if timp_curent - timp_start > timp_maxim:
        raise TimeoutError("DPLL Timp depasit")

    clauze_dupa_bcp, conflict = propaga_unitar(clauze, atribuire, statistici)
    if conflict:
        return None

    clauze_simplificate = clauze_dupa_bcp

    if not clauze_simplificate:
        atribuire_finala = deepcopy(atribuire)
        for variabila in range(1, numar_variabile + 1):
            if variabila not in atribuire_finala:
                atribuire_finala[variabila] = True
        return atribuire_finala

    if any(not c for c in clauze_simplificate):
        return None

    variabila_de_ramificat = selecteaza_variabila_ramificare(atribuire, numar_variabile)

    if variabila_de_ramificat is None:
        return None

    statistici.decizii += 1

    copie_atribuire_adevarat = deepcopy(atribuire)
    copie_atribuire_adevarat[variabila_de_ramificat] = True
    copie_clauze_adevarat = deepcopy(clauze_simplificate)
    rezultat = dpll_recursiv(copie_clauze_adevarat, copie_atribuire_adevarat, numar_variabile, statistici, timp_start,
                             timp_maxim)
    if rezultat is not None:
        return rezultat

    statistici.reveniri += 1

    copie_atribuire_fals = deepcopy(atribuire)
    copie_atribuire_fals[variabila_de_ramificat] = False
    copie_clauze_fals = deepcopy(clauze_simplificate)
    rezultat = dpll_recursiv(copie_clauze_fals, copie_atribuire_fals, numar_variabile, statistici, timp_start,
                             timp_maxim)

    return rezultat


def rezolva_dpll(clauze_intrare, numar_variabile, timp_maxim):
    """Punctul principal de intrare pentru solver-ul DPLL."""
    timp_start = time.perf_counter()
    statistici_dpll = StatisticiDpll()
    atribuire_initiala = {}

    if any(not c for c in clauze_intrare):
        print("DPLL: Formula initiala contine o clauza goala.")
        return "UNSAT", None, statistici_dpll.__dict__

    clauze_curente = deepcopy(clauze_intrare)
    clauze_dupa_bcp, conflict = propaga_unitar(clauze_curente, atribuire_initiala, statistici_dpll)
    if conflict:
        print("DPLL: Conflict detectat in timpul BCP initial.")
        return "UNSAT", None, statistici_dpll.__dict__

    clauze_simplificate = clauze_dupa_bcp

    if not clauze_simplificate:
        print("DPLL: Formula satisfacuta dupa propagarea initiala.")
        atribuire_finala = deepcopy(atribuire_initiala)
        for variabila in range(1, numar_variabile + 1):
            if variabila not in atribuire_finala:
                atribuire_finala[variabila] = True
        return "SAT", atribuire_finala, statistici_dpll.__dict__

    try:
        atribuire_finala = dpll_recursiv(clauze_simplificate, atribuire_initiala, numar_variabile, statistici_dpll,
                                         timp_start, timp_maxim)
        if atribuire_finala is not None:
            for variabila in range(1, numar_variabile + 1):
                if variabila not in atribuire_finala:
                    atribuire_finala[variabila] = True
            return "SAT", atribuire_finala, statistici_dpll.__dict__
        else:
            return "UNSAT", None, statistici_dpll.__dict__
    except TimeoutError:
        return "TIMP_DEPASIT", None, statistici_dpll.__dict__
    except RecursionError:
        print("\nEROARE: Adancimea maxima de recursivitate depasita in DPLL!")
        print(f"Adancimea curenta a atribuirii: {len(atribuire_initiala)} variabile atribuite inainte de eroare.")
        print("Sau problema ar putea fi prea complexa / implementarea necesita optimizare (DPLL iterativ).")
        return "EROARE (Recursivitate)", None, statistici_dpll.__dict__
    except Exception as e:
        print(f"\nA aparut o eroare neasteptata in DPLL: {e}")
        import traceback
        traceback.print_exc()
        return "EROARE (Exceptie)", None, statistici_dpll.__dict__


# --- Functie de Verificare (Optional) ---
def verifica_atribuirea(clauze, atribuire):
    """Verifica daca o atribuire data satisface toate clauzele."""
    if atribuire is None:
        print("Verificare: Nu a fost furnizata nicio atribuire.")
        return False

    toate_satisfacute = True
    for i, clauza in enumerate(clauze):
        clauza_satisfacuta = False
        for literal in clauza:
            variabila = abs(literal)
            este_negat = literal < 0

            if variabila not in atribuire:
                print(
                    f"Eroare Verificare: Variabila {variabila} nu a fost gasita in atribuire pentru clauza {i + 1}: {clauza}")
                toate_satisfacute = False
                break

            valoare_atribuita = atribuire[variabila]
            if (not este_negat and valoare_atribuita is True) or \
                    (este_negat and valoare_atribuita is False):
                clauza_satisfacuta = True
                break

        if not clauza_satisfacuta and toate_satisfacute:
            print(f"Verificare Esuata: Clauza {i + 1} {clauza} NU este satisfacuta de atribuire.")

            toate_satisfacute = False


    if toate_satisfacute:
        print("Verificare Reusita: Atribuirea satisface toate clauzele.")
        return True
    else:
        print("Verificare Esuata: Atribuirea nu satisface toate clauzele.")
        return False


def main():


    FOLOSESTE_FISIER = True  # Seteaza FOLOSESTE_FISIER = True si CALE_FISIER cu numele fisierului (Daca e False se genereaza un test aleatoriu)
    CALE_FISIER = 'test.cnf'  # Exemplu: 'uf20-01.cnf' sau 'uuf50-01.cnf'

    # Parametri pentru generarea FNC daca FOLOSESTE_FISIER este False
    GEN_NUMAR_VARIABILE = 5
    GEN_NUMAR_CLAUZE = 10
    GEN_K = 3
    GEN_ASIGURA_SATISFIABILITATE = False

    # Timpi maximi in secunde pentru fiecare algoritm
    TIMP_MAXIM_REZOLUTIE = 30
    TIMP_MAXIM_DP = 30
    TIMP_MAXIM_DPLL = 3600


    # Selecteaza algoritmii de rulat
    RULEAZA_REZOLUTIE = True
    RULEAZA_DP = True
    RULEAZA_DPLL = True
    VERIFICA_DPLL_SAT = True  # Daca True si DPLL returneaza SAT, ruleaza o verificare

    # --- Sfarsit Configurare ---

    if FOLOSESTE_FISIER:
        print(f"Se incearca incarcarea FNC din: {CALE_FISIER}")
        import os
        if not os.path.exists(CALE_FISIER):
            print(f"Eroare: Fisierul nu a fost gasit la {CALE_FISIER}")
            if CALE_FISIER == 'example.cnf':
                print("Se creeaza un fisier exemplu mic 'example.cnf'.")
                try:
                    with open(CALE_FISIER, 'w') as f:
                        f.write("c Fisier FNC DIMACS exemplu\n")
                        f.write("p cnf 4 4\n")
                        f.write("1 -2 0\n")
                        f.write("2 3 0\n")
                        f.write("-1 -3 0\n")
                        f.write("1 4 0\n")
                    print(f"Fisier exemplu creat {CALE_FISIER}")
                except Exception as e:
                    print(f"Eroare la crearea fisierului exemplu: {e}")
                    return
            else:
                return

        rezultat_parsare = parseaza_dimacs(CALE_FISIER)
        if rezultat_parsare is not None and rezultat_parsare[0] is not None:
            clauze, numar_variabile = rezultat_parsare
        else:
            print("Esec la incarcarea sau parsarea fisierului FNC. Programul se opreste.")
            return
    else:
        print(f"Se genereaza FNC-{GEN_K} aleatoriu cu {GEN_NUMAR_VARIABILE} variabile si {GEN_NUMAR_CLAUZE} clauze...")
        try:
            clauze, numar_variabile = genereaza_fnc(GEN_NUMAR_VARIABILE, GEN_NUMAR_CLAUZE, GEN_K,
                                                    GEN_ASIGURA_SATISFIABILITATE)
            nume_fisier_generat = f"generat_{numar_variabile}v_{len(clauze)}c_{GEN_K}k.cnf"
            try:
                with open(nume_fisier_generat, "w") as f:
                    f.write(f"c FNC-{GEN_K} generat aleatoriu\n")
                    f.write(f"p cnf {numar_variabile} {len(clauze)}\n")
                    for clauza_item in clauze:
                        f.write(" ".join(map(str, clauza_item)) + " 0\n")
                print(f"FNC generat salvat in {nume_fisier_generat}")
            except Exception as e:
                print(f"Eroare la salvarea fisierului generat: {e}")
        except ValueError as e:
            print(f"Eroare in timpul generarii: {e}")
            return

    if clauze is None:
        print("Nicio formula FNC valida nu a fost incarcata sau generata. Programul se opreste.")
        return

    rezultate = {}
    if numar_variabile == 0 and not clauze:
        print("Formula este goala (0 variabile, 0 clauze). Rezultat: SAT")
        rezultate = {'Rezolutie': {'stare': 'SAT', 'timp': 0.0, 'statistici_rulare': {}},
                     'DP': {'stare': 'SAT', 'timp': 0.0, 'statistici_rulare': {}},
                     'DPLL': {'stare': 'SAT', 'timp': 0.0, 'statistici_rulare': {}, 'atribuire': {}}}
    elif numar_variabile > 0 and not clauze:
        print("Formula are variabile dar nu are clauze. Rezultat: SAT")
        atribuire = {v: True for v in range(1, numar_variabile + 1)}
        rezultate = {'Rezolutie': {'stare': 'SAT', 'timp': 0.0, 'statistici_rulare': {}},
                     'DP': {'stare': 'SAT', 'timp': 0.0, 'statistici_rulare': {}},
                     'DPLL': {'stare': 'SAT', 'timp': 0.0, 'statistici_rulare': {}, 'atribuire': atribuire}}
    else:
        print(f"\nFormula incarcata/generata: {numar_variabile} variabile, {len(clauze)} clauze.")

        if RULEAZA_REZOLUTIE:
            print("\n" + "=" * 15 + " Rulare Rezolutie " + "=" * 15)
            timp_s = time.perf_counter()
            stare, _, statistici_rulare = rezolva_prin_rezolutie(clauze, numar_variabile, TIMP_MAXIM_REZOLUTIE)
            timp_e = time.perf_counter()
            durata = timp_e - timp_s
            rezultate['Rezolutie'] = {'stare': stare, 'timp': durata, 'statistici_rulare': statistici_rulare}
            print(f"Rezultat: {stare}")
            print(f"Timp: {durata:.4f} secunde")
            print(f"Statistici: {statistici_rulare}")

        if RULEAZA_DP:
            print("\n" + "=" * 15 + " Rulare Davis-Putnam (Original) " + "=" * 15)
            timp_s = time.perf_counter()
            stare, _, statistici_rulare = rezolva_dp(clauze, numar_variabile, TIMP_MAXIM_DP)
            timp_e = time.perf_counter()
            durata = timp_e - timp_s
            rezultate['DP'] = {'stare': stare, 'timp': durata, 'statistici_rulare': statistici_rulare}
            print(f"Rezultat: {stare} (Nota: DP nu furnizeaza un model)")
            print(f"Timp: {durata:.4f} secunde")
            print(f"Statistici: {statistici_rulare}")

        if RULEAZA_DPLL:
            print("\n" + "=" * 15 + " Rulare DPLL " + "=" * 15)
            timp_s = time.perf_counter()
            stare, atribuire, statistici_rulare = rezolva_dpll(clauze, numar_variabile, TIMP_MAXIM_DPLL)
            timp_e = time.perf_counter()
            durata = timp_e - timp_s
            rezultate['DPLL'] = {'stare': stare, 'timp': durata, 'statistici_rulare': statistici_rulare,
                                 'atribuire': atribuire}
            print(f"Rezultat: {stare}")
            print(f"Timp: {durata:.4f} secunde")
            print(f"Statistici: {statistici_rulare}")
            if stare == "SAT":
                if atribuire:
                    limita_afisare = 20
                    atribuire_limitata = dict(sorted(atribuire.items())[:limita_afisare])
                    sir_atribuire_lim = ", ".join(
                        f"x{v}={('A' if val else 'F')}" for v, val in
                        atribuire_limitata.items())
                    print(
                        f"Atribuire Satisfacatoare (primele {min(limita_afisare, numar_variabile)} variabile afisate):")
                    print(f"  {{{sir_atribuire_lim}{'...' if numar_variabile > limita_afisare else ''}}}")

                    if VERIFICA_DPLL_SAT:
                        print("-" * 10 + " Verificare Atribuire DPLL " + "-" * 10)
                        verifica_atribuirea(clauze, atribuire)
                        print("-" * 40)
                else:
                    print("Avertisment: DPLL a returnat SAT dar atribuirea este goala/None.")

    print("\n" + "=" * 20 + " Sumar " + "=" * 20)
    for algoritm, rez in rezultate.items():
        sir_timp = f"{rez['timp']:.4f}s"
        sir_stare = rez['stare']
        sir_statistici = f"Statistici={rez['statistici_rulare']}" if rez.get('statistici_rulare') else ""

        info_atribuire = ""
        if algoritm == 'DPLL' and rez['stare'] == 'SAT':
            info_atribuire = f"(Atribuire {'gasita' if rez.get('atribuire') else 'lipsa'})"

        print(f"- {algoritm:<12}: Stare={sir_stare:<28} Timp={sir_timp:<10} {sir_statistici} {info_atribuire}")
    print("=" * 50)


if __name__ == "__main__":
    main()
