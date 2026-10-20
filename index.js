import { createServer } from "node:http";
import { readFile } from "node:fs/promises";
import { spawn } from "node:child_process";
import { appendFileSync, closeSync, existsSync, mkdirSync, openSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { freemem } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { gunzipSync, gzipSync } from "node:zlib";

// Gerador pseudoaleatório com semente (mulberry32). Toda a aleatoriedade do arquivo passa por
// aleatorio(), então a mesma semente reproduz exatamente a mesma simulação. A semente muda com
// semear(n) ou com --semente=n na linha de comando.
function mulberry32(semente) {
  let estado = semente >>> 0;
  return () => {
    estado = (estado + 0x6d2b79f5) >>> 0;
    let t = estado;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

let aleatorio = mulberry32(1);

function semear(semente) {
  aleatorio = mulberry32(semente);
}

// Um número em [0, 1) que só depende dos argumentos (inteiros), sem estado: cada argumento entra
// e é misturado com o finalizador do murmur3. Serve para a fiação procedural, que precisa sortear
// a mesma conexão sempre que a consulta, sem guardar nada e sem gastar o gerador da simulação.
function hashUniforme(semente, a, b, c) {
  const misturar = (h) => {
    h ^= h >>> 16;
    h = Math.imul(h, 0x85ebca6b);
    h ^= h >>> 13;
    h = Math.imul(h, 0xc2b2ae35);
    return h ^ (h >>> 16);
  };
  let h = misturar(Math.imul(semente ^ 0x9e3779b9, 0x01000193));
  h = misturar(Math.imul(h ^ a, 0x01000193) + 0x632be59b);
  h = misturar(Math.imul(h ^ b, 0x01000193) + 0x7f4a7c15);
  h = misturar(Math.imul(h ^ c, 0x01000193) + 0x165667b1);
  return (h >>> 0) / 4294967296;
}

// Sem argumento: liga o cérebro com a visualização
function brain() {
  servirVisualizacao(new Cerebro());
}

// ============================================================================
// 01 — Bioeletricidade (neurociencia/01-bioeletricidade.md)
//
// Unidades, salvo indicação: mV, ms, mM.
//   Por área (como no Hodgkin-Huxley): C em µF/cm², g em mS/cm², I em µA/cm²,
//   assim C·dV/dt e g·(V − E) saem ambos em µA/cm².
//   Célula inteira: R em MΩ e I em nA, assim R·I sai em mV.
//   R_m (resistência específica da membrana) em Ω·cm².
// ============================================================================

const CONSTANTE_DOS_GASES = 8.314; // J/(mol·K)
const FARADAY = 96485; // C/mol
const CARGA_ELEMENTAR = 1.602e-19; // C
const AVOGADRO = 6.022e23; // 1/mol

// Concentrações típicas de um neurônio de mamífero (seção 3.1)
const ions = {
  K: { z: 1, dentro: 140, fora: 5 },
  Na: { z: 1, dentro: 12, fora: 145 },
  Cl: { z: -1, dentro: 8, fora: 120 },
  Ca: { z: 2, dentro: 0.0001, fora: 2 },
};

// RT/F em mV (≈ 26,7 mV a 37 °C)
function rtSobreF(temperaturaC = 37) {
  return ((CONSTANTE_DOS_GASES * (temperaturaC + 273.15)) / FARADAY) * 1000;
}

// --- 1. Difusão --------------------------------------------------------------

// t ≈ x²/(2D): o tempo cresce com o quadrado da distância. D em µm²/ms (≈ 1 para íons na água)
function tempoDeDifusao(distanciaUm, d = 1) {
  return distanciaUm ** 2 / (2 * d);
}

// --- 2.2 A membrana como capacitor -------------------------------------------

// Q = C·V numa célula esférica: quantos íons precisam cruzar a membrana para carregá-la até v
function balancoDeCarga({ diametroUm = 25, v = 100, cm = 1, kDentro = 140 } = {}) {
  const cargaPorCm2 = cm * 1e-6 * (v / 1000); // C/cm²
  const ionsPorUm2 = cargaPorCm2 / CARGA_ELEMENTAR / 1e8;
  const areaUm2 = Math.PI * diametroUm ** 2;
  const volumeLitros = (Math.PI / 6) * diametroUm ** 3 * 1e-15;
  const ionsSeparados = ionsPorUm2 * areaUm2;
  const ionsDeK = (kDentro / 1000) * volumeLitros * AVOGADRO;
  return { cargaPorCm2, ionsPorUm2, ionsSeparados, ionsDeK, fracao: ionsSeparados / ionsDeK };
}

// --- 4. Equação de Nernst ----------------------------------------------------

// E = (RT/zF)·ln([fora]/[dentro])
function potencialDeNernst({ z, dentro, fora }, temperaturaC = 37) {
  return (rtSobreF(temperaturaC) / z) * Math.log(fora / dentro);
}

// --- 5.2 Goldman-Hodgkin-Katz ------------------------------------------------

// Permeabilidades relativas. O Cl⁻, por ser negativo, entra com dentro e fora invertidos.
function potencialGHK({ pK, pNa, pCl }, conc = ions, temperaturaC = 37) {
  const { K, Na, Cl } = conc;
  const numerador = pK * K.fora + pNa * Na.fora + pCl * Cl.dentro;
  const denominador = pK * K.dentro + pNa * Na.dentro + pCl * Cl.fora;
  return rtSobreF(temperaturaC) * Math.log(numerador / denominador);
}

// --- 5.3 Forma por condutâncias ----------------------------------------------

// V = Σ gᵢ·Eᵢ / Σ gᵢ: média das baterias ponderada pelos canais abertos. canais = [{ g, e }]
function potencialPorCondutancias(canais) {
  let somaGE = 0;
  let somaG = 0;
  for (const { g, e } of canais) {
    somaGE += g * e;
    somaG += g;
  }
  return somaGE / somaG;
}

// --- 7.2 Equação da membrana (lei de Kirchhoff) ------------------------------

// Σ gᵢ·(V − Eᵢ), em µA/cm²
function correnteIonica(v, canais) {
  let total = 0;
  for (const { g, e } of canais) total += g * (v - e);
  return total;
}

// Um passo de Euler de C·dV/dt = −Σ gᵢ·(V − Eᵢ) + I_ext.
// Cada canal puxa V para o seu Eᵢ, então sem I_ext a voltagem fica entre o menor e o maior Eᵢ
// (no Euler, desde que dt·Σg/C ≤ 1).
function passoMembrana(v, canais, { dt, cm = 1, iExt = 0 }) {
  return v + (dt / cm) * (-correnteIonica(v, canais) + iExt);
}

// --- 7.2–7.3 Integrador com vazamento ----------------------------------------

// τ = R_m·C_m (Ω·cm² · µF/cm² → ms)
function constanteDeTempo(rm, cm = 1) {
  return (rm * cm) / 1000;
}

// Um passo de τ·dV/dt = −(V − E_L) + R·I. Com ruido > 0 (mV/√ms) vira Euler–Maruyama (seção 14.6).
function passoIntegrador(v, { tau, eL, r, ruido = 0 }, entrada, dt) {
  return v + (dt / tau) * (-(v - eL) + r * entrada) + ruido * Math.sqrt(dt) * gaussiana();
}

// Solução exata para um degrau de corrente começando no repouso
function respostaAoDegrau(t, { tau, eL, r }, entrada) {
  return eL + r * entrada * (1 - Math.exp(-t / tau));
}

// --- 7.4 Resistência de entrada e lei de Ohm ---------------------------------

// Célula isopotencial: R_in = R_m / área, em MΩ
function resistenciaDeEntrada(rm, areaUm2) {
  return rm / (areaUm2 * 1e-8) / 1e6;
}

// ΔV = R_in·I (MΩ · nA → mV)
function variacaoDeVoltagem(rEntrada, corrente) {
  return rEntrada * corrente;
}

// --- 8. Teoria do cabo -------------------------------------------------------

// λ = √(R_m·d / 4R_i), com R_i em Ω·cm e diâmetro em µm. Retorna µm.
function constanteDeComprimento({ rm = 20000, ri = 150, diametroUm }) {
  return Math.sqrt((rm * diametroUm * 1e-4) / (4 * ri)) * 1e4;
}

// V(x)/V₀ num cabo semi-infinito, com x em µm. Para freqHz = 0 é e^(−x/λ).
// Num sinal senoidal a capacitância encurta o λ efetivo pelo fator Re√(1 + iωτ):
// sinais rápidos morrem mais perto (filtro passa-baixa).
function atenuacaoNoCabo(x, lambda, { freqHz = 0, tau = 20 } = {}) {
  const omegaTau = 2 * Math.PI * (freqHz / 1000) * tau;
  const fator = Math.sqrt((1 + Math.sqrt(1 + omegaTau ** 2)) / 2);
  return Math.exp((-x / lambda) * fator);
}

// --- 9.5 Canais estocásticos -------------------------------------------------

// I = N·p_aberto·γ·(V − E), com γ em pS. Retorna pA.
function correnteMacroscopica({ n, pAberto, gamma, v, e }) {
  return (n * pAberto * gamma * (v - e)) / 1000;
}

// N canais de dois estados. A cada passo, um canal fechado abre com probabilidade pAbrir
// e um aberto fecha com pFechar. Retorna o número de canais abertos em cada passo.
function simularCanais({ n, pAbrir, pFechar, passos }) {
  let abertos = Math.round((n * pAbrir) / (pAbrir + pFechar));
  const serie = [];
  for (let passo = 0; passo < passos; passo++) {
    let abriram = 0;
    let fecharam = 0;
    for (let i = 0; i < n - abertos; i++) if (aleatorio() < pAbrir) abriram++;
    for (let i = 0; i < abertos; i++) if (aleatorio() < pFechar) fecharam++;
    abertos += abriram - fecharam;
    serie.push(abertos);
  }
  return serie;
}

// Normal padrão (Box–Muller)
function gaussiana() {
  const u = 1 - aleatorio(); // em (0, 1], evita log(0)
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * aleatorio());
}

function media(valores) {
  return valores.reduce((soma, x) => soma + x, 0) / valores.length;
}

function desvioPadrao(valores) {
  const m = media(valores);
  return Math.sqrt(media(valores.map((x) => (x - m) ** 2)));
}

// Saída das demonstrações
const mV = (x) => `${x.toFixed(1)} mV`;
const hz = (f) => `${f.toFixed(1)} Hz`;
const linha = (rotulo, valor) => console.log(`  ${rotulo.padEnd(46)} ${valor}`);

// ============================================================================
// Exemplos do texto e exercícios da seção 15 do 01. Rode com: node index.js --01
// ============================================================================

function demonstracao01() {
  const dt = 0.01; // ms
  const formatarTempo = (ms) => {
    const unidades = [["anos", 3.156e10], ["dias", 8.64e7], ["h", 3.6e6], ["min", 6e4], ["s", 1e3]];
    const [nome, fator] = unidades.find(([, f]) => ms >= f) ?? ["ms", 1];
    return `${(ms / fator).toFixed(1)} ${nome}`;
  };

  console.log("\nDifusão e membrana como capacitor (seções 1 e 2.2)");
  for (const [rotulo, x] of [["1 µm", 1], ["1 mm", 1e3], ["1 m", 1e6]]) {
    linha(`difundir por ${rotulo}`, formatarTempo(tempoDeDifusao(x)));
  }
  const carga = balancoDeCarga();
  linha("Q = C·V (V = 100 mV)", `${carga.cargaPorCm2.toExponential(1)} C/cm²`);
  linha("íons por µm²", carga.ionsPorUm2.toFixed(0));
  linha("íons separados (esfera de 25 µm)", carga.ionsSeparados.toExponential(1));
  linha("íons de K⁺ no citoplasma", carga.ionsDeK.toExponential(1));
  linha("fração que precisou se mover", `1 em ${Math.round(1 / carga.fracao)}`);

  console.log("\nNernst (seção 4.3)");
  const E = {};
  for (const [nome, ion] of Object.entries(ions)) {
    E[nome] = potencialDeNernst(ion);
    linha(`E_${nome}`, mV(E[nome]));
  }

  console.log("\nGHK (seção 5.2 e exercício 1)");
  const conc = { ...ions, Cl: { ...ions.Cl, dentro: 10 } }; // o exemplo da 5.2 usa [Cl⁻] dentro = 10 mM
  const p = { pK: 1, pNa: 0.05, pCl: 0.45 };
  linha("P_K : P_Na : P_Cl = 1 : 0,05 : 0,45", mV(potencialGHK(p, conc)));
  for (const kFora of [5, 10, 20, 40]) {
    linha(`[K⁺] fora = ${kFora} mM`, mV(potencialGHK(p, { ...conc, K: { ...conc.K, fora: kFora } })));
  }
  for (const pNa of [0.01, 0.05, 0.1, 0.2, 0.5]) {
    linha(`P_Na/P_K = ${pNa}`, mV(potencialGHK({ ...p, pNa }, conc)));
  }

  console.log("\nMédia ponderada por condutâncias (seções 4.4 e 5.3)");
  const repouso = { K: 1, Na: 0.1, Cl: 0.2 };
  const comG = (g) => Object.entries(g).map(([nome, gIon]) => ({ g: gIon, e: E[nome] }));
  linha("repouso", mV(potencialPorCondutancias(comG(repouso))));
  linha("abre Na⁺ (g_Na × 200)", mV(potencialPorCondutancias(comG({ ...repouso, Na: 20 }))));
  linha("abre K⁺ (g_K × 10)", mV(potencialPorCondutancias(comG({ ...repouso, K: 10 }))));
  linha("abre Cl⁻ (g_Cl × 25)", mV(potencialPorCondutancias(comG({ ...repouso, Cl: 5 }))));

  console.log("\nMembrana RC (exercício 2)");
  const neuronio = { tau: constanteDeTempo(20000), eL: -70, r: 100 }; // τ = 20 ms, R = 100 MΩ
  const degrau = 0.1; // nA → R·I = 10 mV
  const alvo = neuronio.eL + (1 - Math.exp(-1)) * neuronio.r * degrau;
  let v = neuronio.eL;
  let passos = 0;
  while (v < alvo) {
    v = passoIntegrador(v, neuronio, degrau, dt);
    passos++;
  }
  linha("τ = R_m·C_m", `${neuronio.tau} ms`);
  linha("tempo até 63% do valor final (Euler)", `${(passos * dt).toFixed(2)} ms`);
  linha("V(τ) pela solução exata", mV(respostaAoDegrau(neuronio.tau, neuronio, degrau)));

  console.log("\nSomação temporal: dois pulsos de 1 ms e 2 nA (exercício 3)");
  for (const intervalo of [1, 5, 20, 100]) {
    let vPulsos = neuronio.eL;
    let pico = vPulsos;
    const total = Math.round((intervalo + 5 * neuronio.tau) / dt);
    for (let passo = 0; passo < total; passo++) {
      const t = passo * dt;
      const ligado = t < 1 || (t >= intervalo && t < intervalo + 1);
      vPulsos = passoIntegrador(vPulsos, neuronio, ligado ? 2 : 0, dt);
      pico = Math.max(pico, vPulsos);
    }
    linha(`Δt = ${intervalo} ms`, `pico ${(pico - neuronio.eL).toFixed(1)} mV acima do repouso`);
  }

  console.log("\nSinapse por corrente × por condutância, regime estacionário (exercício 4 e seção 14.2)");
  const vazamento = { g: 0.05, e: -70 }; // mS/cm²; τ = C/g = 20 ms
  const sinapse = { g: 0.01, e: 0 }; // excitatória, reverte em 0 mV
  const iSinapse = sinapse.g * (sinapse.e - vazamento.e); // a mesma sinapse vista como corrente fixa
  for (const n of [1, 10, 100]) {
    let vCorrente = vazamento.e;
    let vCondutancia = vazamento.e;
    for (let passo = 0; passo < 200 / dt; passo++) {
      vCorrente = passoMembrana(vCorrente, [vazamento], { dt, iExt: n * iSinapse });
      vCondutancia = passoMembrana(vCondutancia, [vazamento, { g: n * sinapse.g, e: sinapse.e }], { dt });
    }
    linha(`${n} entrada(s) simultânea(s)`, `corrente ${mV(vCorrente)} · condutância ${mV(vCondutancia)}`);
  }

  console.log("\nResistência de entrada e lei de Ohm (seção 7.4)");
  for (const diametroUm of [25, 100]) {
    const rEntrada = resistenciaDeEntrada(20000, Math.PI * diametroUm ** 2);
    linha(`soma esférico de ${diametroUm} µm`, `R_in = ${rEntrada.toFixed(0)} MΩ → 10 pA dão ${mV(variacaoDeVoltagem(rEntrada, 0.01))}`);
  }

  console.log("\nTeoria do cabo (seção 8)");
  for (const diametroUm of [0.5, 1, 2]) {
    linha(`λ com d = ${diametroUm} µm`, `${constanteDeComprimento({ diametroUm }).toFixed(0)} µm`);
  }
  const lambda = constanteDeComprimento({ diametroUm: 1 });
  for (const freqHz of [0, 10, 100]) {
    const sobra = atenuacaoNoCabo(300, lambda, { freqHz, tau: neuronio.tau });
    linha(`a 300 µm, sinal de ${freqHz} Hz`, `${(100 * sobra).toFixed(0)}% da amplitude`);
  }
  // e^(−2000) não cabe num double, então o resultado sai como potência de 10
  linha("axônio passivo de 1 m (λ = 0,5 mm)", `sobra 10^${(-1e6 / 500 / Math.LN10).toFixed(0)} do sinal`);

  console.log("\nCanais estocásticos (seção 9.5 e exercício 5)");
  const pAbrir = 0.1;
  const pFechar = 0.1;
  const pAberto = pAbrir / (pAbrir + pFechar);
  for (const n of [10, 100, 10000]) {
    const serie = simularCanais({ n, pAbrir, pFechar, passos: 2000 });
    const ruido = desvioPadrao(serie) / media(serie);
    const teoria = Math.sqrt((1 - pAberto) / (n * pAberto));
    linha(`N = ${n}`, `ruído relativo ${(100 * ruido).toFixed(1)}% (teoria ${(100 * teoria).toFixed(1)}%)`);
  }
  const iNa = correnteMacroscopica({ n: 1000, pAberto, gamma: 20, v: -20, e: E.Na });
  linha("1000 canais de Na⁺ a −20 mV (γ = 20 pS)", `${iNa.toFixed(0)} pA`);

  const ruidoso = { ...neuronio, ruido: 1 };
  const amostras = [];
  let vRuido = neuronio.eL;
  for (let passo = 0; passo < 20000 / dt; passo++) {
    vRuido = passoIntegrador(vRuido, ruidoso, 0, dt);
    if (passo % 100 === 0) amostras.push(vRuido);
  }
  linha("membrana com ruído σ = 1 mV/√ms", `desvio ${mV(desvioPadrao(amostras))} (teoria ${mV(Math.sqrt(neuronio.tau / 2))})`);
}

// ============================================================================
// 02 — O neurônio (neurociencia/02-neuronio.md)
//
// Hodgkin-Huxley usa as unidades por área do 01 (µF/cm², mS/cm², µA/cm²) e o LIF as de célula
// inteira (MΩ, nA). Izhikevich usa as do artigo original (v em mV, corrente adimensional) e o
// AdEx usa pF, nS e pA. Todo modelo com spike segue a mesma interface:
//   { criar() → estado, passo(estado, corrente, dt) → true se disparou }
// ============================================================================

// --- 3. Hodgkin-Huxley -------------------------------------------------------

const parametrosHH = { cm: 1, gNa: 120, eNa: 50, gK: 36, eK: -77, gL: 0.3, eL: -54.4 };

// x / (1 − e^(−x/k)), com o limite k em x = 0 (evita 0/0 em α_m e α_n)
function razaoExponencial(x, k) {
  return Math.abs(x) < 1e-7 ? k : x / (1 - Math.exp(-x / k));
}

// Taxas de abertura (α) e fechamento (β) dos portões m, h e n, em 1/ms
function taxasHH(v) {
  return {
    m: { alfa: 0.1 * razaoExponencial(v + 40, 10), beta: 4 * Math.exp(-(v + 65) / 18) },
    h: { alfa: 0.07 * Math.exp(-(v + 65) / 20), beta: 1 / (1 + Math.exp(-(v + 35) / 10)) },
    n: { alfa: 0.01 * razaoExponencial(v + 55, 10), beta: 0.125 * Math.exp(-(v + 65) / 80) },
  };
}

// Para cada portão: x∞ = α/(α+β) e τ = 1/(α+β)
function portoesEmEquilibrio(v) {
  const portoes = {};
  for (const [nome, { alfa, beta }] of Object.entries(taxasHH(v))) {
    portoes[nome] = { infinito: alfa / (alfa + beta), tau: 1 / (alfa + beta) };
  }
  return portoes;
}

function criarHH(v = -65) {
  const { m, h, n } = portoesEmEquilibrio(v);
  return { v, m: m.infinito, h: h.infinito, n: n.infinito };
}

// Um passo de Euler das 4 EDOs. A voltagem é a equação da membrana do 01 com g_Na = ḡ·m³h
// e g_K = ḡ·n⁴; cada portão segue dx/dt = α(V)(1 − x) − β(V)·x.
function passoHH(s, corrente, dt, p = parametrosHH) {
  const taxas = taxasHH(s.v);
  const canais = [
    { g: p.gNa * s.m ** 3 * s.h, e: p.eNa },
    { g: p.gK * s.n ** 4, e: p.eK },
    { g: p.gL, e: p.eL },
  ];
  s.v = passoMembrana(s.v, canais, { dt, cm: p.cm, iExt: corrente });
  for (const x of ["m", "h", "n"]) {
    const { alfa, beta } = taxas[x];
    s[x] += dt * (alfa * (1 - s[x]) - beta * s[x]);
  }
  return s;
}

// O HH não tem reset: conta um spike quando V cruza 0 mV subindo
const modeloHH = {
  criar: () => criarHH(),
  passo: (s, corrente, dt) => {
    const antes = s.v;
    passoHH(s, corrente, dt);
    return antes < 0 && s.v >= 0;
  },
};

// --- 11.1 LIF, com adaptação opcional (13.1) ---------------------------------

// τ·dV/dt = −(V − E_L) + R·I − w. Se V ≥ V_limiar: spike, V ← V_reset e refratário por t_ref.
// A adaptação w (mV) sobe incrementoW a cada spike e decai com τ_w; com incrementoW = 0 é o LIF puro.
const parametrosLIF = { tau: 20, eL: -65, r: 100, vLimiar: -50, vReset: -65, tRef: 2, tauW: 200, incrementoW: 0, ruido: 0 };

function criarLIF(p = parametrosLIF) {
  return { v: p.eL, w: 0, refratario: 0 };
}

function passoLIF(s, p, corrente, dt) {
  s.w -= (dt / p.tauW) * s.w;
  if (s.refratario > 0) {
    s.refratario -= dt;
    return false;
  }
  s.v = passoIntegrador(s.v, p, corrente - s.w / p.r, dt);
  if (s.v < p.vLimiar) return false;
  s.v = p.vReset;
  s.w += p.incrementoW;
  s.refratario = p.tRef;
  return true;
}

function modeloLIF(p = parametrosLIF) {
  return { criar: () => criarLIF(p), passo: (s, corrente, dt) => passoLIF(s, p, corrente, dt) };
}

// Curva f-I exata do LIF sem adaptação nem ruído, em Hz. Satura em 1/t_ref.
// f = 1 / (t_ref + τ·ln((R·I − (V_reset − E_L)) / (R·I − (V_limiar − E_L))))
function frequenciaLIF(p, corrente) {
  const ri = p.r * corrente;
  if (ri <= p.vLimiar - p.eL) return 0;
  return 1000 / (p.tRef + p.tau * Math.log((ri - (p.vReset - p.eL)) / (ri - (p.vLimiar - p.eL))));
}

// --- 11.2 Izhikevich ---------------------------------------------------------

// dv/dt = 0,04v² + 5v + 140 − u + I;  du/dt = a(bv − u);  se v ≥ 30 mV: v ← c e u ← u + d
const tiposIzhikevich = {
  regular: { a: 0.02, b: 0.2, c: -65, d: 8 },
  rajada: { a: 0.02, b: 0.2, c: -55, d: 4 },
  tagarela: { a: 0.02, b: 0.2, c: -50, d: 2 },
  rapido: { a: 0.1, b: 0.2, c: -65, d: 2 },
  limiarBaixo: { a: 0.02, b: 0.25, c: -65, d: 2 },
};

function criarIzhikevich({ b }, v = -65) {
  return { v, u: b * v };
}

// No passo do spike u não é integrado, porque o v desse passo pode ter passado muito de 30 mV
function passoIzhikevich(s, { a, b, c, d }, corrente, dt) {
  s.v += dt * (0.04 * s.v * s.v + 5 * s.v + 140 - s.u + corrente);
  if (s.v >= 30) {
    s.v = c;
    s.u += d;
    return true;
  }
  s.u += dt * a * (b * s.v - s.u);
  return false;
}

function modeloIzhikevich(tipo) {
  return { criar: () => criarIzhikevich(tipo), passo: (s, corrente, dt) => passoIzhikevich(s, tipo, corrente, dt) };
}

// --- 11. AdEx (Brette & Gerstner, 2005) ---------------------------------------

// C·dV/dt = −g_L(V − E_L) + g_L·Δ_T·e^((V − V_T)/Δ_T) − w + I;  τ_w·dw/dt = a(V − E_L) − w
// Se V ≥ V_pico: V ← V_reset e w ← w + b. O termo exponencial é o início explosivo do spike.
const parametrosAdEx = { c: 281, gL: 30, eL: -70.6, vT: -50.4, deltaT: 2, tauW: 144, a: 4, b: 80.5, vReset: -70.6, vPico: 20 };

function criarAdEx(p = parametrosAdEx) {
  return { v: p.eL, w: 0 };
}

function passoAdEx(s, p, corrente, dt) {
  const inicioDoSpike = p.gL * p.deltaT * Math.exp((s.v - p.vT) / p.deltaT);
  const dw = (p.a * (s.v - p.eL) - s.w) / p.tauW;
  s.v += (dt / p.c) * (-p.gL * (s.v - p.eL) + inicioDoSpike - s.w + corrente);
  s.w += dt * dw;
  if (s.v < p.vPico) return false;
  s.v = p.vReset;
  s.w += p.b;
  return true;
}

function modeloAdEx(p = parametrosAdEx) {
  return { criar: () => criarAdEx(p), passo: (s, corrente, dt) => passoAdEx(s, p, corrente, dt) };
}

// --- 6. Padrões de disparo e curva f-I ----------------------------------------

// Tempos dos spikes (ms) de um modelo com corrente constante ou corrente(t)
function tempoDosSpikes(modelo, corrente, duracao, dt) {
  const s = modelo.criar();
  const tempos = [];
  const total = Math.round(duracao / dt);
  for (let passo = 0; passo < total; passo++) {
    const i = typeof corrente === "function" ? corrente(passo * dt) : corrente;
    if (modelo.passo(s, i, dt)) tempos.push(passo * dt);
  }
  return tempos;
}

// Intervalos entre spikes (ms)
function intervalos(tempos) {
  return tempos.slice(1).map((t, i) => t - tempos[i]);
}

// Curva f-I: frequência (Hz) para cada corrente constante, medida depois de um transiente
function curvaFI(modelo, correntes, { duracao = 1000, transiente = 200, dt = 0.05 } = {}) {
  return correntes.map((corrente) => {
    const tempos = tempoDosSpikes(modelo, corrente, duracao, dt).filter((t) => t >= transiente);
    return (1000 * tempos.length) / (duracao - transiente);
  });
}

// --- 7. Dendritos ---------------------------------------------------------------

// Somação passiva no mesmo ramo (7.2): as sinapses são condutâncias e cada uma reduz a força
// eletromotriz (V − E) da outra, então a soma é sublinear. Devolve a despolarização em mV.
function despolarizacaoNoRamo(condutancias, { gL = 0.05, eL = -70, eSinapse = 0 } = {}) {
  return potencialPorCondutancias([{ g: gL, e: eL }, ...condutancias.map((g) => ({ g, e: eSinapse }))]) - eL;
}

function sigmoide(x, limiar = 0, inclinacao = 1) {
  return 1 / (1 + Math.exp(-(x - limiar) * inclinacao));
}

// Poirazi, Brannon & Mel (2003): cada ramo aplica a sua sigmoide à soma das suas sinapses
// (spike de NMDA: soma supralinear) e o soma soma os ramos. É uma rede de duas camadas.
// ramos = [{ pesos, limiar, inclinacao }]; entradas[i] é o vetor de entradas do ramo i.
function neuronioDeDuasCamadas(ramos, entradas) {
  return ramos.reduce((soma, ramo, i) => {
    const local = ramo.pesos.reduce((total, w, j) => total + w * entradas[i][j], 0);
    return soma + sigmoide(local, ramo.limiar, ramo.inclinacao);
  }, 0);
}

// Gidon et al. (2020): a amplitude do potencial dendrítico de Ca²⁺ é máxima no limiar e cai
// para entradas mais fortes. Essa resposta não monotônica deixa um único ramo computar XOR.
function respostaEmSino(x, limiar, largura) {
  return x < limiar ? 0 : Math.exp(-(x - limiar) / largura);
}

// --- 4. Propagação -------------------------------------------------------------

// Sem mielina: v ≈ √d (m/s com d em µm), que dá ~1 m/s numa fibra C e ~22 m/s no axônio gigante
// de lula. Com mielina: lei de Hursh, v ≈ 6·d, que reproduz a tabela da seção 4.2.
function velocidadeDeConducao(diametroUm, mielinizado = false) {
  return mielinizado ? 6 * diametroUm : Math.sqrt(diametroUm);
}

// Distância entre nodos de Ranvier (µm): ~100 vezes o diâmetro
function comprimentoDoInternodo(diametroUm) {
  return 100 * diametroUm;
}

// ============================================================================
// Exemplos do texto e exercícios da seção 14 do 02. Rode com: node index.js --02
// ============================================================================

function demonstracao02() {
  const listaMs = (valores) => valores.map((x) => x.toFixed(1)).join(", ");

  console.log("\nHodgkin-Huxley: portões em −65 mV (seção 3.3)");
  const repouso = portoesEmEquilibrio(-65);
  for (const x of ["m", "h", "n"]) {
    linha(`τ_${x}`, `${repouso[x].tau.toFixed(2)} ms (${x}∞ = ${repouso[x].infinito.toFixed(3)})`);
  }

  // Pulsos de 1 ms: [{ inicio, amplitude }]. Devolve os spikes e o maior V.
  const pulsosHH = (pulsos, duracao = 40, dt = 0.01) => {
    const s = criarHH();
    let pico = s.v;
    let spikes = 0;
    for (let passo = 0; passo < duracao / dt; passo++) {
      const t = passo * dt;
      const corrente = pulsos.reduce((total, { inicio, amplitude }) => total + (t >= inicio && t < inicio + 1 ? amplitude : 0), 0);
      if (modeloHH.passo(s, corrente, dt)) spikes++;
      pico = Math.max(pico, s.v);
    }
    return { spikes, pico };
  };

  console.log("\nHH: tudo ou nada com um pulso de 1 ms (seção 2.2 e exercício 2a)");
  for (const amplitude of [3, 5, 7, 10, 20, 40]) {
    const { spikes, pico } = pulsosHH([{ inicio: 5, amplitude }]);
    linha(`${amplitude} µA/cm²`, `pico ${mV(pico)}${spikes ? " → spike" : ""}`);
  }

  console.log("\nHH: período refratário, dois pulsos de 20 µA/cm² (exercício 2b)");
  for (const intervalo of [2, 4, 6, 8, 10, 12, 16]) {
    const { spikes } = pulsosHH([{ inicio: 5, amplitude: 20 }, { inicio: 5 + intervalo, amplitude: 20 }]);
    linha(`intervalo de ${intervalo} ms`, spikes === 2 ? "o segundo pulso dispara" : "o segundo pulso falha");
  }

  console.log("\nHH: curva f-I com corrente constante (exercício 2c)");
  const correntesHH = [5, 6, 6.5, 7, 8, 10, 15, 20];
  curvaFI(modeloHH, correntesHH, { dt: 0.01 }).forEach((f, i) => linha(`${correntesHH[i]} µA/cm²`, hz(f)));

  console.log("\nLIF: curva f-I exata × simulada × com ruído (seção 11.1 e exercício 1)");
  const comRuido = { ...parametrosLIF, ruido: 1 };
  const correntesLIF = [0.1, 0.14, 0.16, 0.2, 0.3, 0.5, 2, 10];
  const simuladas = curvaFI(modeloLIF(), correntesLIF, { duracao: 2000 });
  const ruidosas = curvaFI(modeloLIF(comRuido), correntesLIF, { duracao: 2000 });
  correntesLIF.forEach((corrente, i) => {
    linha(`${corrente} nA`, `exata ${hz(frequenciaLIF(parametrosLIF, corrente))} · simulada ${hz(simuladas[i])} · com ruído ${hz(ruidosas[i])}`);
  });

  console.log("\nClasse I × classe II: menor frequência acima de zero (seção 6.3)");
  const menorFrequencia = (modelo, correntes, dt) => Math.min(...curvaFI(modelo, correntes, { dt, duracao: 3000, transiente: 1000 }).filter((f) => f > 0));
  linha("LIF (integrador, classe I)", hz(menorFrequencia(modeloLIF(), [0.1501, 0.1505, 0.151, 0.155], 0.05)));
  linha("Izhikevich regular (classe I)", hz(menorFrequencia(modeloIzhikevich(tiposIzhikevich.regular), [4.001, 4.01, 4.05, 4.1], 0.05)));
  linha("Hodgkin-Huxley (ressonador, classe II)", hz(menorFrequencia(modeloHH, [6, 6.1, 6.2, 6.3, 6.5, 7, 8, 9, 10], 0.01)));

  console.log("\nIzhikevich: os padrões de disparo com I = 10 por 300 ms (seção 11.2 e exercício 3)");
  for (const [nome, tipo] of Object.entries(tiposIzhikevich)) {
    const tempos = tempoDosSpikes(modeloIzhikevich(tipo), (t) => (t >= 20 ? 10 : 0), 320, 0.1);
    linha(`${nome} (${tempos.length} spikes)`, `intervalos: ${listaMs(intervalos(tempos).slice(0, 7))} ms`);
  }

  console.log("\nAdEx: adaptação com um degrau de 1 nA (seção 11)");
  const temposAdEx = tempoDosSpikes(modeloAdEx(), 1000, 400, 0.05);
  linha(`${temposAdEx.length} spikes em 400 ms`, `intervalos: ${listaMs(intervalos(temposAdEx).slice(0, 7))} ms`);

  console.log("\nLIF com e sem adaptação, degrau de 0,3 nA por 1 s (seção 13.1 e exercício 4)");
  const adaptativo = { ...parametrosLIF, incrementoW: 2 };
  for (const [nome, p] of [["sem adaptação", parametrosLIF], ["com adaptação", adaptativo]]) {
    const isi = intervalos(tempoDosSpikes(modeloLIF(p), 0.3, 1000, 0.05));
    linha(nome, `${isi.length + 1} spikes · primeiro intervalo ${isi[0].toFixed(1)} ms · último ${isi.at(-1).toFixed(1)} ms`);
  }
  const fSem = curvaFI(modeloLIF(), [0.2, 0.3, 0.5]);
  const fCom = curvaFI(modeloLIF(adaptativo), [0.2, 0.3, 0.5]);
  [0.2, 0.3, 0.5].forEach((corrente, i) => linha(`f-I em ${corrente} nA`, `sem ${hz(fSem[i])} · com ${hz(fCom[i])}`));

  console.log("\nDendritos: somação passiva sublinear no mesmo ramo (seção 7.2)");
  const uma = despolarizacaoNoRamo([0.02]);
  linha("uma sinapse", mV(uma));
  linha("duas sinapses no mesmo ramo", `${mV(despolarizacaoNoRamo([0.02, 0.02]))} (a soma linear daria ${mV(2 * uma)})`);

  console.log("\nDendritos: neurônio de duas camadas, 4 ramos com 4 sinapses (seções 7.3, 7.5 e 13.4)");
  const ramos = Array.from({ length: 4 }, () => ({ pesos: [1, 1, 1, 1], limiar: 1.5, inclinacao: 6 }));
  const agrupadas = [[1, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]];
  const espalhadas = [[1, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]];
  linha("2 entradas no mesmo ramo (\"gato E preto\")", neuronioDeDuasCamadas(ramos, agrupadas).toFixed(3));
  linha("as mesmas 2 entradas em ramos diferentes", neuronioDeDuasCamadas(ramos, espalhadas).toFixed(3));

  console.log("\nDendritos: XOR com um ramo em forma de sino (seção 7.5 e exercício 6)");
  for (const [a, b] of [[0, 0], [1, 0], [0, 1], [1, 1]]) {
    const resposta = respostaEmSino(a + b, 1, 0.3);
    linha(`A = ${a}, B = ${b}`, `ramo ${resposta.toFixed(3)} → saída ${resposta > 0.5 ? 1 : 0}`);
  }

  console.log("\nVelocidade de condução e latência em 1 m (seção 4)");
  const fibras = [["fibra C, 1 µm, sem mielina", 1, false], ["axônio de lula, 500 µm, sem mielina", 500, false], ["Aδ, 3 µm", 3, true], ["Aβ, 9 µm", 9, true], ["Aα, 16 µm", 16, true]];
  for (const [nome, d, mielinizado] of fibras) {
    const v = velocidadeDeConducao(d, mielinizado);
    const internodo = mielinizado ? ` · internodo ${(comprimentoDoInternodo(d) / 1000).toFixed(1)} mm` : "";
    linha(nome, `${v.toFixed(1)} m/s · ${(1000 / v).toFixed(0)} ms por metro${internodo}`);
  }
}

// ============================================================================
// 03 — A sinapse (neurociencia/03-sinapse.md)
// ============================================================================

// --- 5.2 Liberação quântica: o modelo binomial -------------------------------

function amostraBinomial(n, p) {
  let k = 0;
  for (let i = 0; i < n; i++) if (aleatorio() < p) k++;
  return k;
}

// Uma resposta: k ~ Binomial(n, p) vesículas liberadas, cada uma de tamanho q. Em média, n·p·q.
function respostaQuantica({ n, p, q }) {
  return amostraBinomial(n, p) * q;
}

// Recupera n, p e q a partir das amplitudes: q é o menor degrau não nulo, e as equações
// média = n·p·q e variância = n·p·(1 − p)·q² dão p e depois n.
function estimarParametrosQuanticos(amplitudes) {
  const q = Math.min(...amplitudes.filter((a) => a > 0));
  const m = media(amplitudes);
  const p = 1 - desvioPadrao(amplitudes) ** 2 / (m * q);
  return { n: m / (p * q), p, q };
}

// --- 4.2 Cooperatividade do cálcio -------------------------------------------

// Probabilidade de liberação em função do Ca²⁺ local (µM): uma Hill de expoente 4, que cresce
// com [Ca²⁺]⁴ longe da saturação (Dodge & Rahamimoff, 1967)
function probabilidadeDeLiberacao(calcio, { kd = 20, n = 4, pMax = 1 } = {}) {
  return (pMax * calcio ** n) / (calcio ** n + kd ** n);
}

// --- 7.2 Bloqueio do NMDA por Mg²⁺ -------------------------------------------

// Fração desbloqueada (Jahr & Stevens, 1990), com [Mg²⁺] em mM. A condutância efetiva é g·B(V),
// então só passa corrente com glutamato E despolarização.
function bloqueioMg(v, mg = 1) {
  return 1 / (1 + (mg / 3.57) * Math.exp(-0.062 * v));
}

// --- 7 e 8 Condutâncias pós-sinápticas -----------------------------------------

// Constantes de decaimento (ms)
const tausSinapticos = { ampa: 5, nmda: 100, gabaA: 10, gabaB: 200 };

// Decaimento exponencial exato de uma condutância num passo dt
function decair(g, tau, dt) {
  return g * Math.exp(-dt / tau);
}

// --- 8.2 Pesos lognormais ------------------------------------------------------

function amostraLognormal(mediana, sigma) {
  return mediana * Math.exp(sigma * gaussiana());
}

// --- 11.2 Plasticidade de curto prazo: Tsodyks-Markram -------------------------

// x: fração de vesículas disponíveis; u: fração usada por spike. Entre spikes as EDOs
// dx/dt = (1 − x)/τ_rec e du/dt = (U − u)/τ_fac são lineares, então uso a solução exata.
// Sem τ_fac (sinapse só depressora), u fica fixo em U.
function criarSinapseTM({ U }) {
  return { x: 1, u: U, ultimoSpike: -Infinity };
}

// Um spike no tempo t (ms): atualiza u, libera u·x e gasta isso de x. Devolve a liberação.
function liberarTM(s, { U, tauRec, tauFac = 0 }, t) {
  const intervalo = t - s.ultimoSpike;
  s.x = 1 - (1 - s.x) * Math.exp(-intervalo / tauRec);
  if (tauFac > 0) {
    s.u = U + (s.u - U) * Math.exp(-intervalo / tauFac);
    s.u += U * (1 - s.u);
  }
  const liberacao = s.u * s.x;
  s.x -= liberacao;
  s.ultimoSpike = t;
  return liberacao;
}

// --- 12. Sinalização metabotrópica ---------------------------------------------

// Cada etapa da cascata multiplica o sinal (receptor → proteínas G → cAMP → PKA → ...)
function ganhoDaCascata(ganhos) {
  return ganhos.reduce((total, ganho) => total * ganho, 1);
}

// Adenilato ciclase tipo 1: produto de duas saturações, então só responde a Ca²⁺ E Gs juntos
function adenilatoCiclase1(calcio, gs, { kCalcio = 1, kGs = 1 } = {}) {
  return (calcio / (calcio + kCalcio)) * (gs / (gs + kGs));
}

// --- Entradas Poisson -------------------------------------------------------------

// Um processo de Poisson com taxa em Hz dispara num passo dt (ms)?
function spikePoisson(taxaHz, dt) {
  return aleatorio() < (taxaHz * dt) / 1000;
}

// Número de eventos de Poisson com média lambda (algoritmo de Knuth, bom para lambda pequeno)
function amostraPoisson(lambda) {
  const limite = Math.exp(-lambda);
  let k = 0;
  let produto = aleatorio();
  while (produto > limite) {
    k++;
    produto *= aleatorio();
  }
  return k;
}

// ============================================================================
// Exemplos do texto e exercícios da seção 17 do 03. Rode com: node index.js --03
// ============================================================================

function demonstracao03() {
  console.log("\nLiberação binomial: n = 5, p = 0,3, q = 0,4 mV, 1000 spikes (seção 5.2 e exercício 1)");
  const quantico = { n: 5, p: 0.3, q: 0.4 };
  const amplitudes = Array.from({ length: 1000 }, () => respostaQuantica(quantico));
  const combinacoes = (n, k) => (k === 0 ? 1 : (combinacoes(n, k - 1) * (n - k + 1)) / k);
  for (let k = 0; k <= quantico.n; k++) {
    const contagem = amplitudes.filter((a) => Math.round(a / quantico.q) === k).length;
    const esperado = 1000 * combinacoes(quantico.n, k) * quantico.p ** k * (1 - quantico.p) ** (quantico.n - k);
    linha(`${(k * quantico.q).toFixed(1)} mV (${k} quanta)`, `${contagem} respostas (binomial: ${esperado.toFixed(0)})`);
  }
  const estimado = estimarParametrosQuanticos(amplitudes);
  linha("resposta média (n·p·q = 0,60 mV)", `${media(amplitudes).toFixed(2)} mV`);
  linha("estimado pela média e pela variância", `n = ${estimado.n.toFixed(1)} · p = ${estimado.p.toFixed(2)} · q = ${estimado.q.toFixed(2)} mV`);

  console.log("\nCooperatividade do cálcio (seção 4.2)");
  for (const calcio of [5, 6, 10, 20, 40]) {
    linha(`[Ca²⁺] local = ${calcio} µM`, `p = ${probabilidadeDeLiberacao(calcio).toFixed(4)}`);
  }
  linha("+20% de cálcio (5 → 6 µM)", `liberação × ${(probabilidadeDeLiberacao(6) / probabilidadeDeLiberacao(5)).toFixed(2)}`);

  console.log("\nBloqueio do NMDA por Mg²⁺ = 1 mM (seção 7.2)");
  for (const v of [-80, -60, -40, -20, 0]) {
    linha(`V = ${v} mV`, `${(100 * bloqueioMg(v)).toFixed(1)}% desbloqueado`);
  }

  console.log("\nInibição por shunting × hiperpolarizante, despolarização estacionária (seção 9.1)");
  const vazamento = { g: 0.05, e: -65 };
  const shunting = { g: 0.05, e: -65 };
  const hiperpolarizante = { g: 0.05, e: -80 };
  for (const gE of [0, 0.01, 0.02, 0.04]) {
    const despolarizacao = (inibicao) => mV(potencialPorCondutancias([vazamento, { g: gE, e: 0 }, ...inibicao]) - vazamento.e);
    linha(`g_E = ${gE}`, `sem inibição ${despolarizacao([])} · shunting ${despolarizacao([shunting])} · hiperpolarizante ${despolarizacao([hiperpolarizante])}`);
  }

  console.log("\nShunting na frequência de disparo, sem ruído (seção 9.1: Holt & Koch, 1997)");
  // LIF por área: τ = C/g e R = 1/g, com C = 1 µF/cm²
  const lifPorCondutancia = (gTotal) => ({ ...parametrosLIF, tau: 1 / gTotal, r: 1 / gTotal, tRef: 0 });
  for (const corrente of [2, 4, 8, 16]) {
    const sem = frequenciaLIF(lifPorCondutancia(0.05), corrente);
    const com = frequenciaLIF(lifPorCondutancia(0.1), corrente);
    linha(`${corrente} µA/cm²`, `sem ${hz(sem)} · com shunting ${hz(com)} · diferença ${hz(sem - com)} · razão ${(com / sem).toFixed(2)}`);
  }

  console.log("\nPesos lognormais: 10.000 EPSPs com mediana 0,5 mV e σ = 1 (seção 8.2)");
  const epsps = Array.from({ length: 10000 }, () => amostraLognormal(0.5, 1)).sort((a, b) => b - a);
  const soma = (valores) => valores.reduce((total, x) => total + x, 0);
  linha("mediana · média", `${epsps[5000].toFixed(2)} mV · ${media(epsps).toFixed(2)} mV`);
  linha("parte do total nos 10% mais fortes", `${((100 * soma(epsps.slice(0, 1000))) / soma(epsps)).toFixed(0)}%`);
  linha("conexões acima de 2 mV", `${((100 * epsps.filter((x) => x > 2).length) / epsps.length).toFixed(1)}%`);

  console.log("\nTsodyks-Markram: trem de 10 spikes a 20 Hz, liberação relativa ao 1º (seção 11 e exercício 2)");
  const depressora = { U: 0.5, tauRec: 800 };
  const facilitadora = { U: 0.05, tauRec: 100, tauFac: 1000 };
  for (const [nome, p] of [["depressora", depressora], ["facilitadora", facilitadora]]) {
    const s = criarSinapseTM(p);
    const liberacoes = Array.from({ length: 10 }, (_, k) => liberarTM(s, p, k * 50));
    linha(nome, liberacoes.map((l) => (l / liberacoes[0]).toFixed(2)).join("  "));
  }

  console.log("\nTsodyks-Markram: Poisson que salta de 10 para 40 Hz em t = 2 s, liberação por segundo (média de 200)");
  const janelas = [["antes (1–2 s)", 1000, 2000], ["logo depois (2–2,2 s)", 2000, 2200], ["adaptada (3–4 s)", 3000, 4000]];
  for (const [nome, p] of [["depressora", depressora], ["facilitadora", facilitadora]]) {
    const somas = janelas.map(() => 0);
    for (let repeticao = 0; repeticao < 200; repeticao++) {
      const s = criarSinapseTM(p);
      for (let t = 0; t < 4000; t++) {
        if (!spikePoisson(t < 2000 ? 10 : 40, 1)) continue;
        const liberacao = liberarTM(s, p, t);
        janelas.forEach(([, inicio, fim], j) => {
          if (t >= inicio && t < fim) somas[j] += liberacao;
        });
      }
    }
    janelas.forEach(([rotulo, inicio, fim], j) => linha(`${nome}, ${rotulo}`, (somas[j] / 200 / ((fim - inicio) / 1000)).toFixed(2)));
  }

  console.log("\nAMPA (τ = 5 ms) + NMDA (τ = 100 ms) com bloqueio de Mg²⁺, uma entrada (exercício 3)");
  const dt = 0.05;
  for (const vInicial of [-70, -55, -40]) {
    const membrana = { g: 0.05, e: -70 };
    const iSegurar = membrana.g * (vInicial - membrana.e); // corrente que segura V em vInicial
    let v = vInicial;
    let gA = 0.01;
    let gN = 0.01;
    const pico = { a: 0, n: 0 };
    const carga = { a: 0, n: 0 };
    for (let passo = 0; passo < 300 / dt; passo++) {
      const gNEfetiva = gN * bloqueioMg(v);
      pico.a = Math.max(pico.a, gA * -v);
      pico.n = Math.max(pico.n, gNEfetiva * -v);
      carga.a += gA * -v * dt;
      carga.n += gNEfetiva * -v * dt;
      v = passoMembrana(v, [membrana, { g: gA, e: 0 }, { g: gNEfetiva, e: 0 }], { dt, iExt: iSegurar });
      gA = decair(gA, tausSinapticos.ampa, dt);
      gN = decair(gN, tausSinapticos.nmda, dt);
    }
    linha(`partindo de ${vInicial} mV`, `pico NMDA/AMPA ${((100 * pico.n) / pico.a).toFixed(0)}% · carga NMDA/AMPA ${(carga.n / carga.a).toFixed(1)}×`);
  }

  console.log("\nCascata metabotrópica e adenilato ciclase tipo 1 (seção 12.2)");
  linha("1 receptor → 20 G → ×100 cAMP → ×10 PKA", `${ganhoDaCascata([20, 100, 10])} moléculas no fim`);
  for (const [calcio, gs] of [[0, 0], [5, 0], [0, 5], [5, 5]]) {
    linha(`Ca²⁺ ${calcio ? "alto" : "zero"}, Gs ${gs ? "ativo" : "inativo"}`, `AC1 = ${adenilatoCiclase1(calcio, gs).toFixed(2)}`);
  }
}

// ============================================================================
// 04 — Plasticidade sináptica (neurociencia/04-plasticidade.md)
// As regras de taxa recebem vetores (arrays) e alteram os pesos no lugar.
// ============================================================================

function produtoEscalar(a, b) {
  return a.reduce((total, x, i) => total + x * b[i], 0);
}

function norma(v) {
  return Math.sqrt(produtoEscalar(v, v));
}

// --- 2, 11.2 e 7.2 Regras de taxa ---------------------------------------------

// Hebb: Δw = η·x·y
function hebb(w, x, y, eta) {
  for (let i = 0; i < w.length; i++) w[i] += eta * x[i] * y;
}

// Covariância: Δw = η·(x − x̄)(y − ȳ). Permite LTD quando só um dos lados está acima da média.
function covariancia(w, x, y, xMedio, yMedio, eta) {
  for (let i = 0; i < w.length; i++) w[i] += eta * (x[i] - xMedio[i]) * (y - yMedio);
}

// Oja: Δw = η·y·(x − y·w). O termo −y²·w é um decaimento que segura |w| ≈ 1, e w converge para
// a primeira componente principal das entradas.
function oja(w, x, y, eta) {
  for (let i = 0; i < w.length; i++) w[i] += eta * y * (x[i] - y * w[i]);
}

// BCM: dw/dt = η·x·y·(y − θ_M). LTP com y acima do limiar, LTD abaixo.
function bcm(w, x, y, theta, eta) {
  for (let i = 0; i < w.length; i++) w[i] += eta * x[i] * y * (y - theta);
}

// O limiar desliza: θ_M acompanha ⟨y²⟩/y₀ por uma média móvel com constante τ (em passos)
function atualizarLimiarBCM(theta, y, { y0 = 1, tau = 10 } = {}) {
  return theta + ((y * y) / y0 - theta) / tau;
}

// --- 9. STDP --------------------------------------------------------------------

// Janela em pares, com Δt = t_pós − t_pré (ms). A₋ um pouco maior que A₊ dá dominância de LTD.
// Numa simulação ela é aplicada com traços: cada neurônio guarda um traço que soma 1 por spike e
// decai com τ. Num spike pré, Δw = −A₋·traço_pós; num spike pós, Δw = +A₊·traço_pré.
const parametrosSTDP = { aMais: 0.005, aMenos: 0.00525, tauMais: 20, tauMenos: 20 };

function janelaSTDP(dt, p = parametrosSTDP) {
  if (dt > 0) return p.aMais * Math.exp(-dt / p.tauMais);
  if (dt < 0) return -p.aMenos * Math.exp(dt / p.tauMenos);
  return 0;
}

// Regra de tripletos (Pfister & Gerstner, 2006), parâmetros mínimos do córtex visual.
// Traços r1, r2 no pré e o1, o2 no pós (+1 por spike, cada um com o seu τ).
// Spike pré: Δw = −o1·(A2₋ + A3₋·r2). Spike pós: Δw = +r1·(A2₊ + A3₊·o2).
// Os traços lentos entram com o valor de antes do spike e fazem a regra depender da frequência.
const parametrosTripletos = { a2Mais: 5e-10, a3Mais: 6.2e-3, a2Menos: 7e-3, a3Menos: 0, tauMais: 16.8, tauMenos: 33.7, tauX: 101, tauY: 125 };

function criarTracosTripletos() {
  return { r1: 0, r2: 0, o1: 0, o2: 0, t: 0 };
}

// Um spike pré (lado = "pre") ou pós no tempo t. Devolve Δw.
function tripletos(tr, lado, t, p = parametrosTripletos) {
  const dt = t - tr.t;
  tr.r1 *= Math.exp(-dt / p.tauMais);
  tr.r2 *= Math.exp(-dt / p.tauX);
  tr.o1 *= Math.exp(-dt / p.tauMenos);
  tr.o2 *= Math.exp(-dt / p.tauY);
  tr.t = t;
  if (lado === "pre") {
    const dw = -tr.o1 * (p.a2Menos + p.a3Menos * tr.r2);
    tr.r1 += 1;
    tr.r2 += 1;
    return dw;
  }
  const dw = tr.r1 * (p.a2Mais + p.a3Mais * tr.o2);
  tr.o1 += 1;
  tr.o2 += 1;
  return dw;
}

// Regra baseada em voltagem (Clopath et al., 2010). ū₋ e ū₊ são a voltagem pós filtrada com
// τ₋ e τ₊, e x̄ é o traço pré (τ_x·dx̄/dt = −x̄ + spikes).
//   LTD a cada spike pré: Δw = −A_LTD·[ū₋ − θ₋]₊
//   LTP contínua:         dw/dt = A_LTP·x̄·[u − θ₊]₊·[ū₊ − θ₋]₊
const parametrosClopath = { aLTD: 14e-5, aLTP: 8e-5, thetaMenos: -70.6, thetaMais: -45.3, tauMenos: 10, tauMais: 7, tauX: 15 };

function criarSinapseClopath(vRepouso = -70.6) {
  return { w: 0.5, uMenos: vRepouso, uMais: vRepouso, xBarra: 0 };
}

function passoClopath(s, u, preDisparou, dt, p = parametrosClopath) {
  if (preDisparou) s.w -= p.aLTD * Math.max(0, s.uMenos - p.thetaMenos);
  s.w += dt * p.aLTP * s.xBarra * Math.max(0, u - p.thetaMais) * Math.max(0, s.uMais - p.thetaMenos);
  s.uMenos += (dt / p.tauMenos) * (u - s.uMenos);
  s.uMais += (dt / p.tauMais) * (u - s.uMais);
  s.xBarra += -(dt / p.tauX) * s.xBarra + (preDisparou ? 1 / p.tauX : 0);
}

// --- 7.1 Regras de cálcio ----------------------------------------------------------

// Versão da seção 18.1: uma variável de "cálcio" decide a direção. Acima de θ_p: LTP com limite
// suave; entre θ_d e θ_p: LTD; abaixo de θ_d: nada. Devolve Δw.
function mudancaPorCalcio(calcio, w, { thetaD = 0.35, thetaP = 0.55, etaP = 0.1, etaD = 0.05, wMax = 1 } = {}) {
  if (calcio > thetaP) return etaP * (wMax - w);
  if (calcio > thetaD) return -etaD * w;
  return 0;
}

// Graupner & Brunel (2012): o cálcio soma saltos do pré (com atraso D) e do pós e decai com τ_Ca.
// τ·dρ/dt = −ρ(1 − ρ)(ρ* − ρ) + γ_p(1 − ρ)·Θ(c − θ_p) − γ_d·ρ·Θ(c − θ_d) + ruído
// O primeiro termo deixa ρ biestável: 0 (sinapse fraca) e 1 (forte). Tempos em ms.
const parametrosGB = { tauCa: 20, cPre: 1, cPos: 2, atraso: 13.7, thetaD: 1, thetaP: 1.3, gamaD: 200, gamaP: 321.808, tau: 150000, rhoEstrela: 0.5, sigma: 2.8284 };

function passoGraupnerBrunel(rho, calcio, dt, p = parametrosGB, comRuido = false) {
  let tendencia = -rho * (1 - rho) * (p.rhoEstrela - rho);
  if (calcio > p.thetaP) tendencia += p.gamaP * (1 - rho);
  if (calcio > p.thetaD) tendencia -= p.gamaD * rho;
  let novo = rho + (dt / p.tau) * tendencia;
  if (comRuido && calcio > p.thetaD) novo += p.sigma * Math.sqrt(dt / p.tau) * gaussiana();
  return Math.min(1, Math.max(0, novo));
}

// --- 11.2 Limites dos pesos -----------------------------------------------------------

function limiteRigido(w, wMax) {
  return Math.min(wMax, Math.max(0, w));
}

// Limites suaves: a LTP é proporcional ao que falta até w_max e a LTD é proporcional a w
function ltpSuave(w, eta, wMax) {
  return eta * (wMax - w);
}

function ltdSuave(w, eta) {
  return -eta * w;
}

// --- 11.2–11.5 Homeostase ---------------------------------------------------------------

// Escalonamento sináptico: w ← w·(1 + ε(r_alvo − r̄)). Todas as entradas do neurônio são
// multiplicadas pelo mesmo fator, então as proporções aprendidas ficam iguais.
function escalonamentoSinaptico(pesos, taxaMedia, taxaAlvo, epsilon) {
  const fator = 1 + epsilon * (taxaAlvo - taxaMedia);
  for (let i = 0; i < pesos.length; i++) pesos[i] *= fator;
}

// Normalização: mantém a soma dos pesos de um neurônio igual a `total`
function normalizarSoma(pesos, total = 1) {
  const soma = pesos.reduce((s, w) => s + w, 0);
  for (let i = 0; i < pesos.length; i++) pesos[i] *= total / soma;
}

// Heterossináptica: potenciar uma entrada tira o mesmo total das outras, proporcionalmente
// ao peso de cada uma, e o orçamento do neurônio fica constante
function plasticidadeHeterossinaptica(pesos, indice, delta) {
  const outras = pesos.reduce((s, w, i) => (i === indice ? s : s + w), 0);
  pesos[indice] += delta;
  if (outras <= 0) return;
  for (let i = 0; i < pesos.length; i++) if (i !== indice) pesos[i] -= (delta * pesos[i]) / outras;
}

// iSTDP (Vogels et al., 2011) numa sinapse inibitória, com traços de τ = 20 ms.
// Spike pré: Δw = η(traço_pós − α). Spike pós: Δw = η·traço_pré.
// Em média a regra para quando a taxa pós vale ρ₀ = α/(2τ).
function alfaVogels(taxaAlvoHz, tau = 20) {
  return 2 * (taxaAlvoHz / 1000) * tau;
}

function istdpPre(w, tracoPos, alfa, eta) {
  return Math.max(0, w + eta * (tracoPos - alfa));
}

function istdpPos(w, tracoPre, eta) {
  return w + eta * tracoPre;
}

// --- Três fatores (tabela 16) ---------------------------------------------------------------

// A elegibilidade guarda a coincidência pré-pós e decai com τ_e. O modulador M(t) (dopamina,
// novidade) decide se ela vira mudança de peso: dw/dt = η·e·M.
function passoTresFatores(s, coincidencia, modulador, dt, { tauE = 1000, eta = 0.001 } = {}) {
  s.elegibilidade += -(dt / tauE) * s.elegibilidade + coincidencia;
  s.w += eta * s.elegibilidade * modulador * dt;
}

// --- 10. BTSP ---------------------------------------------------------------------------------

// Janela de segundos em volta do platô dendrítico, assimétrica: favorece entradas que vieram
// antes. Δt = t_entrada − t_platô (ms). Constantes aproximadas a partir de Bittner et al. (2017).
function janelaBTSP(dt, { tauAntes = 1300, tauDepois = 700 } = {}) {
  return dt <= 0 ? Math.exp(dt / tauAntes) : Math.exp(-dt / tauDepois);
}

// --- 8.2 e 18.4–18.5 Marcação e captura, peso rápido + lento (tempo em minutos) ---------------

// Toda LTP entra em wRapido, que decai em ~1 h, e deixa uma etiqueta que dura ~1–2 h. Quando um
// evento forte libera "proteínas", conexões etiquetadas passam wRapido para wLento, que não decai.
function criarPesoConsolidavel() {
  return { wRapido: 0, wLento: 0, etiqueta: 0 };
}

function potenciar(c, quanto) {
  c.wRapido += quanto;
  c.etiqueta = 1;
}

function passoConsolidacao(c, proteinas, dt, { tauRapido = 60, tauEtiqueta = 90, taxaCaptura = 0.1 } = {}) {
  const captura = taxaCaptura * proteinas * c.etiqueta * c.wRapido * dt;
  c.wRapido += -(dt / tauRapido) * c.wRapido - captura;
  c.wLento += captura;
  c.etiqueta -= (dt / tauEtiqueta) * c.etiqueta;
}

// Peso como cadeia de m variáveis com escalas de tempo crescentes (inspirado em Benna & Fusi, 2016).
// C_k·du_k/dt = g_{k−1}(u_{k−1} − u_k) + g_k(u_{k+1} − u_k), com C_k = 2^k, g_k = 2^(−k−2) e
// u_m = 0. A mudança entra em u₀ e escoa para os níveis lentos, e a memória em u₀ decai como uma
// lei de potência em vez de uma exponencial.
function passoCadeia(u, dt) {
  const fluxos = u.map((uk, k) => 2 ** (-k - 2) * (uk - (k + 1 < u.length ? u[k + 1] : 0)));
  for (let k = 0; k < u.length; k++) u[k] += (dt / 2 ** k) * ((k > 0 ? fluxos[k - 1] : 0) - fluxos[k]);
}

// --- 5.3 Interruptor biestável (CaMKII; Lisman, 1985) -------------------------------------------

// Autoativação cooperativa contra desfosforilação: dx/dt = −x/τ + k·xⁿ/(Kⁿ + xⁿ) + estímulo.
// Com estes parâmetros há dois estados estáveis (x = 0 e x ≈ 1,84) separados por x = 1.
function passoInterruptor(x, estimulo, dt, { tau = 10, k = 0.2, kMeio = 1, n = 4 } = {}) {
  return x + dt * (-x / tau + (k * x ** n) / (kMeio ** n + x ** n) + estimulo);
}

// --- 12.1 Informação por sinapse ----------------------------------------------------------------

function bitsPorSinapse(tamanhosDistinguiveis) {
  return Math.log2(tamanhosDistinguiveis);
}

// ============================================================================
// Simulações dos exercícios do 04
// ============================================================================

// LIF por condutância das simulações de Song e Vogels (condutâncias em unidades do vazamento)
const lifSong = { tau: 20, eL: -70, vLimiar: -54, vReset: -60, eExc: 0, eInib: -70, tauSinapse: 5 };

// Song, Miller & Abbott (2000): um LIF recebe 1000 entradas excitatórias Poisson com STDP e 200
// inibitórias fixas. As primeiras `nCorrelacionadas` copiam, cada uma com probabilidade c, os
// spikes de uma fonte comum. Devolve a taxa de saída no começo e no fim e os pesos finais / g_max.
function simularSong({ limites = "rigidos", duracaoS = 200, nEntradas = 1000, nCorrelacionadas = 200, c = 0.2, taxaHz = 10, dt = 0.25 } = {}) {
  const gMax = 0.015;
  const { aMais, aMenos, tauMais, tauMenos } = { ...parametrosSTDP, aMenos: 1.05 * parametrosSTDP.aMais };
  const w = Array.from({ length: nEntradas }, () => aleatorio() * gMax);
  const tracoPre = new Float64Array(nEntradas);
  const tempoPre = new Float64Array(nEntradas);
  let tracoPos = 0;
  let v = lifSong.eL;
  let gExc = 0;
  let gInib = 0;
  const spikes = [];
  const decaimentoSinapse = Math.exp(-dt / lifSong.tauSinapse);
  const decaimentoPos = Math.exp(-dt / tauMenos);

  const preDisparou = (i, t) => {
    gExc += w[i];
    const dw = limites === "rigidos" ? -aMenos * gMax * tracoPos : ltdSuave(w[i], aMenos * tracoPos);
    w[i] = limiteRigido(w[i] + dw, gMax);
    tracoPre[i] = tracoPre[i] * Math.exp(-(t - tempoPre[i]) / tauMais) + 1;
    tempoPre[i] = t;
  };

  const total = Math.round((duracaoS * 1000) / dt);
  for (let passo = 0; passo < total; passo++) {
    const t = passo * dt;
    for (let k = amostraPoisson(((nEntradas - nCorrelacionadas) * taxaHz * dt) / 1000); k > 0; k--) {
      preDisparou(nCorrelacionadas + Math.floor(aleatorio() * (nEntradas - nCorrelacionadas)), t);
    }
    for (let k = amostraPoisson((nCorrelacionadas * taxaHz * (1 - c) * dt) / 1000); k > 0; k--) {
      preDisparou(Math.floor(aleatorio() * nCorrelacionadas), t);
    }
    if (spikePoisson(taxaHz, dt)) {
      for (let i = 0; i < nCorrelacionadas; i++) if (aleatorio() < c) preDisparou(i, t);
    }
    gInib += 0.05 * amostraPoisson((200 * 10 * dt) / 1000);

    v += (dt / lifSong.tau) * (lifSong.eL - v + gExc * (lifSong.eExc - v) + gInib * (lifSong.eInib - v));
    gExc *= decaimentoSinapse;
    gInib *= decaimentoSinapse;
    tracoPos *= decaimentoPos;
    if (v < lifSong.vLimiar) continue;

    v = lifSong.vReset;
    spikes.push(t);
    for (let i = 0; i < nEntradas; i++) {
      const traco = tracoPre[i] * Math.exp(-(t - tempoPre[i]) / tauMais);
      const dw = limites === "rigidos" ? aMais * gMax * traco : ltpSuave(w[i], aMais * traco, gMax);
      w[i] = limiteRigido(w[i] + dw, gMax);
    }
    tracoPos += 1;
  }

  const taxaEntre = (inicio, fim) => spikes.filter((t) => t >= inicio && t < fim).length / ((fim - inicio) / 1000);
  return {
    taxaInicial: taxaEntre(0, 10000),
    taxaFinal: taxaEntre((duracaoS - 10) * 1000, duracaoS * 1000),
    correlacionadas: w.slice(0, nCorrelacionadas).map((x) => x / gMax),
    independentes: w.slice(nCorrelacionadas).map((x) => x / gMax),
  };
}

// Vogels et al. (2011): o mesmo LIF com 800 entradas excitatórias fixas (peso wExc) e 200
// inibitórias com iSTDP. Devolve a taxa de saída no começo e no fim e o peso inibitório médio.
function simularVogels({ wExc, taxaAlvoHz = 5, duracaoS = 60, eta = 0.001, dt = 0.25 } = {}) {
  const nInib = 200;
  const tau = 20;
  const alfa = alfaVogels(taxaAlvoHz, tau);
  const w = new Float64Array(nInib);
  const tracoPre = new Float64Array(nInib);
  const tempoPre = new Float64Array(nInib);
  let tracoPos = 0;
  let v = lifSong.eL;
  let gExc = 0;
  let gInib = 0;
  const spikes = [];
  const decaimentoSinapse = Math.exp(-dt / lifSong.tauSinapse);
  const decaimentoPos = Math.exp(-dt / tau);

  const total = Math.round((duracaoS * 1000) / dt);
  for (let passo = 0; passo < total; passo++) {
    const t = passo * dt;
    gExc += wExc * amostraPoisson((800 * 10 * dt) / 1000);
    for (let k = amostraPoisson((nInib * 10 * dt) / 1000); k > 0; k--) {
      const i = Math.floor(aleatorio() * nInib);
      gInib += w[i];
      w[i] = istdpPre(w[i], tracoPos, alfa, eta);
      tracoPre[i] = tracoPre[i] * Math.exp(-(t - tempoPre[i]) / tau) + 1;
      tempoPre[i] = t;
    }

    v += (dt / lifSong.tau) * (lifSong.eL - v + gExc * (lifSong.eExc - v) + gInib * (-80 - v));
    gExc *= decaimentoSinapse;
    gInib *= decaimentoSinapse;
    tracoPos *= decaimentoPos;
    if (v < lifSong.vLimiar) continue;

    v = lifSong.vReset;
    spikes.push(t);
    for (let i = 0; i < nInib; i++) w[i] = istdpPos(w[i], tracoPre[i] * Math.exp(-(t - tempoPre[i]) / tau), eta);
    tracoPos += 1;
  }

  const taxaEntre = (inicio, fim) => spikes.filter((t) => t >= inicio && t < fim).length / ((fim - inicio) / 1000);
  return { taxaInicial: taxaEntre(0, 5000), taxaFinal: taxaEntre((duracaoS - 10) * 1000, duracaoS * 1000), pesoMedio: media(Array.from(w)) };
}

// Rede recorrente de taxa com Hebb e, se epsilon > 0, escalonamento sináptico (exercício 7).
// Devolve a taxa média em alguns pontos, ou o passo em que a atividade explodiu.
function simularHebbComEscalonamento({ epsilon, passos = 6000, n = 20, eta = 1e-4, taxaAlvo = 1 } = {}) {
  const W = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 0 : 0.02 * aleatorio())));
  const entrada = Array.from({ length: n }, () => 0.5 + 0.5 * aleatorio());
  let r = new Array(n).fill(0);
  const rMedia = new Array(n).fill(0);
  const pontos = [];
  for (let passo = 1; passo <= passos; passo++) {
    r = W.map((pesos, i) => Math.max(0, produtoEscalar(pesos, r) + entrada[i]));
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) if (i !== j) W[i][j] += eta * r[i] * r[j];
      rMedia[i] += (r[i] - rMedia[i]) / 20;
      if (epsilon > 0) escalonamentoSinaptico(W[i], rMedia[i], taxaAlvo, epsilon);
    }
    if (media(r) > 1e6) return { explodiu: passo, pontos };
    if (passo % (passos / 4) === 0) pontos.push(media(r));
  }
  return { pontos };
}

// Mudança de ρ de Graupner-Brunel depois de `pares` pares pré-pós com Δt = t_pós − t_pré
function stdpGraupnerBrunel(delta, { pares = 60, frequenciaHz = 1, dt = 0.1 } = {}, p = parametrosGB) {
  const periodo = 1000 / frequenciaHz;
  const eventos = [];
  for (let k = 0; k < pares; k++) {
    const pre = 200 + k * periodo;
    eventos.push({ t: pre + p.atraso, salto: p.cPre }, { t: pre + delta, salto: p.cPos });
  }
  eventos.sort((a, b) => a.t - b.t);
  const decaimento = Math.exp(-dt / p.tauCa);
  let rho = 0.5;
  let calcio = 0;
  let proximo = 0;
  const total = Math.round((pares * periodo + 400) / dt);
  for (let passo = 0; passo < total; passo++) {
    while (proximo < eventos.length && eventos[proximo].t <= passo * dt) calcio += eventos[proximo++].salto;
    rho = passoGraupnerBrunel(rho, calcio, dt, p);
    calcio *= decaimento;
  }
  return rho - 0.5;
}

// Δw total da regra de tripletos depois de `pares` pares com Δt = t_pós − t_pré
function protocoloTripletos(delta, frequenciaHz, pares = 60) {
  const periodo = 1000 / frequenciaHz;
  const eventos = [];
  for (let k = 0; k < pares; k++) {
    eventos.push({ t: 100 + k * periodo, lado: "pre" }, { t: 100 + k * periodo + delta, lado: "pos" });
  }
  eventos.sort((a, b) => a.t - b.t);
  const tr = criarTracosTripletos();
  return eventos.reduce((dw, { t, lado }) => dw + tripletos(tr, lado, t), 0);
}

// Δw da regra de Clopath num AdEx. O spike pós é forçado no tempo certo e dura 2 ms a 29,4 mV,
// como no artigo, porque a regra lê a forma da voltagem.
function protocoloClopath(delta, frequenciaHz, pares = 60, dt = 0.1) {
  const periodo = 1000 / frequenciaHz;
  const passosPre = new Set();
  const passosPos = new Set();
  for (let k = 0; k < pares; k++) {
    passosPre.add(Math.round((100 + k * periodo) / dt));
    passosPos.add(Math.round((100 + k * periodo + delta) / dt));
  }
  const neuronio = criarAdEx();
  const sinapse = criarSinapseClopath(parametrosAdEx.eL);
  let spikeRestante = 0;
  const total = Math.round((pares * periodo + 200) / dt);
  for (let passo = 0; passo < total; passo++) {
    if (passosPos.has(passo)) spikeRestante = 2;
    if (spikeRestante > 0) {
      neuronio.v = 29.4;
      spikeRestante -= dt;
      if (spikeRestante <= 0) {
        neuronio.v = parametrosAdEx.vReset;
        neuronio.w += parametrosAdEx.b;
      }
    } else {
      passoAdEx(neuronio, parametrosAdEx, 0, dt);
    }
    passoClopath(sinapse, neuronio.v, passosPre.has(passo), dt);
  }
  return sinapse.w - 0.5;
}

// ============================================================================
// Exemplos do texto e exercícios da seção 19 do 04. Rode com: node index.js --04
// ============================================================================

function demonstracao04() {
  const histograma = (valores, caixas = 10) => {
    const contagens = new Array(caixas).fill(0);
    for (const x of valores) contagens[Math.min(caixas - 1, Math.floor(x * caixas))]++;
    const maior = Math.max(...contagens);
    return contagens.map((n) => " ▁▂▃▄▅▆▇█"[Math.round((8 * n) / maior)]).join("");
  };
  const porcentagem = (x) => `${x >= 0 ? "+" : ""}${(100 * x).toFixed(1)}%`;

  console.log("\nHebb explode, Oja acha a 1ª componente principal (seção 11.2 e exercício 1)");
  const direcao = Array.from({ length: 10 }, (_, i) => 1 + i / 5);
  const amostra = () => {
    const s = gaussiana();
    return direcao.map((a) => s * a + 0.5 * gaussiana());
  };
  const dados = Array.from({ length: 5000 }, amostra);
  let componente = new Array(10).fill(1);
  for (let iteracao = 0; iteracao < 100; iteracao++) {
    const proxima = componente.map((_, i) => media(dados.map((x) => x[i] * produtoEscalar(x, componente))));
    componente = proxima.map((c) => c / norma(proxima));
  }
  const wHebb = Array.from({ length: 10 }, () => 0.1 * aleatorio());
  const wOja = [...wHebb];
  const normasHebb = [];
  dados.forEach((x, passo) => {
    hebb(wHebb, x, produtoEscalar(wHebb, x), 0.001);
    oja(wOja, x, produtoEscalar(wOja, x), 0.001);
    if ([10, 100, 1000, 4999].includes(passo)) normasHebb.push(norma(wHebb).toExponential(1));
  });
  linha("|w| de Hebb nos passos 10, 100, 1000, 5000", normasHebb.join(" → "));
  linha("|w| de Oja no fim", norma(wOja).toFixed(3));
  linha("cosseno entre w de Oja e a 1ª componente", Math.abs(produtoEscalar(wOja, componente) / norma(wOja)).toFixed(4));

  console.log("\nCovariância: LTD quando só um lado está acima da média (tabela 16)");
  for (const [x, y] of [[1, 1], [1, 0], [0, 1], [0, 0]]) {
    const w = [0.5];
    covariancia(w, [x], y, [0.5], 0.5, 0.1);
    linha(`pré ${x ? "alto" : "baixo"}, pós ${y ? "alto" : "baixo"}`, `Δw = ${(w[0] - 0.5).toFixed(3)}`);
  }

  console.log("\nBCM: um neurônio com dois padrões alternados fica seletivo (seção 7.2 e exercício 2)");
  const padroes = [[1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 1, 1, 1]];
  for (let rodada = 1; rodada <= 5; rodada++) {
    const w = Array.from({ length: 10 }, () => 0.2 + 0.1 * aleatorio());
    let theta = 1;
    for (let k = 0; k < 20000; k++) {
      const x = padroes[aleatorio() < 0.5 ? 0 : 1];
      const y = Math.max(0, produtoEscalar(w, x));
      bcm(w, x, y, theta, 0.002);
      for (let i = 0; i < w.length; i++) w[i] = Math.max(0, w[i]);
      theta = atualizarLimiarBCM(theta, y, { tau: 20 });
    }
    const respostas = padroes.map((x) => produtoEscalar(w, x));
    linha(`rodada ${rodada}`, `resposta ao padrão A ${respostas[0].toFixed(2)} · ao B ${respostas[1].toFixed(2)} · θ_M ${theta.toFixed(2)}`);
  }

  console.log("\nSTDP em pares: a janela (seção 9.2)");
  linha("Δt (ms)", [-40, -20, -10, -5, 5, 10, 20, 40].map((d) => String(d).padStart(7)).join(""));
  linha("Δw (×10⁻³)", [-40, -20, -10, -5, 5, 10, 20, 40].map((d) => (1000 * janelaSTDP(d)).toFixed(2).padStart(7)).join(""));

  console.log("\nSTDP competitivo de Song, Miller & Abbott: 500 s, 200 de 1000 entradas correlacionadas (exercício 3)");
  for (const limites of ["rigidos", "suaves"]) {
    const r = simularSong({ limites, duracaoS: 500 });
    linha(`limites ${limites}: taxa de saída`, `${hz(r.taxaInicial)} nos primeiros 10 s → ${hz(r.taxaFinal)} nos últimos`);
    linha(`limites ${limites}: peso médio / g_max`, `correlacionadas ${media(r.correlacionadas).toFixed(2)} · independentes ${media(r.independentes).toFixed(2)}`);
    linha(`limites ${limites}: histograma 0 → g_max`, `correlacionadas [${histograma(r.correlacionadas)}]  independentes [${histograma(r.independentes)}]`);
  }

  console.log("\nTripletos: 60 pares com |Δt| = 10 ms em várias frequências (seção 9.5 e exercício 4)");
  for (const frequencia of [1, 10, 20, 40, 50]) {
    linha(`${frequencia} Hz`, `pré→pós ${porcentagem(protocoloTripletos(10, frequencia))} · pós→pré ${porcentagem(protocoloTripletos(-10, frequencia))}`);
  }

  console.log("\nRegra por voltagem de Clopath, o mesmo protocolo num AdEx (seção 9.5)");
  for (const frequencia of [1, 10, 20, 40, 50]) {
    linha(`${frequencia} Hz`, `pré→pós ${porcentagem(protocoloClopath(10, frequencia))} · pós→pré ${porcentagem(protocoloClopath(-10, frequencia))}`);
  }

  console.log("\nRegra de cálcio com dois limiares, 10 eventos partindo de w = 0,5 (seções 7.1 e 18.1)");
  for (const [nome, calcio] of [["cálcio baixo (0,2)", 0.2], ["cálcio moderado (0,45)", 0.45], ["cálcio alto (0,8)", 0.8]]) {
    let w = 0.5;
    for (let evento = 0; evento < 10; evento++) w += mudancaPorCalcio(calcio, w);
    linha(nome, `w = ${w.toFixed(3)}`);
  }

  console.log("\nGraupner-Brunel: Δρ depois de 60 pares a 1 Hz, partindo de ρ = 0,5 (seção 7.1 e exercício 5)");
  const deltas = [-60, -30, -15, -5, 0, 5, 15, 30, 60];
  linha("Δt (ms)", deltas.map((d) => String(d).padStart(7)).join(""));
  linha("Δρ", deltas.map((d) => stdpGraupnerBrunel(d).toFixed(3).padStart(7)).join(""));

  console.log("\nHebb + escalonamento numa rede recorrente de 20 neurônios, alvo = 1 (seção 11 e exercício 7)");
  for (const [nome, epsilon] of [["sem escalonamento", 0], ["escalonamento lento (ε = 10⁻³)", 1e-3], ["escalonamento rápido (ε = 10⁻¹)", 1e-1]]) {
    const r = simularHebbComEscalonamento({ epsilon });
    const trajetoria = r.pontos.map((x) => x.toFixed(2)).join(" → ");
    linha(nome, r.explodiu ? `explodiu no passo ${r.explodiu}${trajetoria ? ` (${trajetoria})` : ""}` : `taxa média ${trajetoria}`);
  }
  const pesos = [0.2, 0.4, 0.8];
  escalonamentoSinaptico(pesos, 3, 1, 0.1);
  linha("escalonamento de [0,2 0,4 0,8] com r̄ = 3", `[${pesos.map((w) => w.toFixed(2)).join(" ")}]: as razões 1 : 2 : 4 continuam`);

  console.log("\nOrçamento sináptico (seções 11.2 e 11.4)");
  const orcamento = [0.2, 0.3, 0.5];
  plasticidadeHeterossinaptica(orcamento, 0, 0.1);
  linha("heterossináptica: potencia a 1ª em 0,1", `[${orcamento.map((w) => w.toFixed(3)).join(" ")}] soma ${orcamento.reduce((s, w) => s + w, 0).toFixed(3)}`);
  const normalizados = [1, 3, 6];
  normalizarSoma(normalizados);
  linha("normalização de [1 3 6] para soma 1", `[${normalizados.map((w) => w.toFixed(2)).join(" ")}]`);

  console.log("\niSTDP de Vogels: a inibição se ajusta até a taxa-alvo de 5 Hz (seção 11.5)");
  for (const wExc of [0.01, 0.015]) {
    const r = simularVogels({ wExc });
    linha(`excitação com peso ${wExc}`, `${hz(r.taxaInicial)} nos primeiros 5 s → ${hz(r.taxaFinal)} nos últimos 10 s · peso inibitório médio ${r.pesoMedio.toFixed(3)}`);
  }

  console.log("\nTrês fatores: recompensa (dopamina) de 100 ms em t = 1 s (tabela 16)");
  for (const [nome, tCoincidencia, comRecompensa] of [["coincidência em 0,5 s", 500, true], ["coincidência em 2,5 s", 2500, true], ["coincidência em 0,5 s, sem recompensa", 500, false]]) {
    const s = { w: 0, elegibilidade: 0 };
    for (let t = 0; t < 4000; t++) {
      const modulador = comRecompensa && t >= 1000 && t < 1100 ? 1 : 0;
      passoTresFatores(s, t === tCoincidencia ? 1 : 0, modulador, 1);
    }
    linha(nome, `Δw = ${s.w.toFixed(3)}`);
  }

  console.log("\nBTSP: janela de segundos em volta do platô (seção 10)");
  const atrasos = [-3000, -2000, -1000, 0, 1000, 2000];
  linha("entrada − platô (s)", atrasos.map((d) => String(d / 1000).padStart(6)).join(""));
  linha("Δw relativo", atrasos.map((d) => janelaBTSP(d).toFixed(2).padStart(6)).join(""));
  let somaPeso = 0;
  let somaPesoTempo = 0;
  for (let d = -5000; d <= 5000; d += 10) {
    somaPeso += janelaBTSP(d);
    somaPesoTempo += d * janelaBTSP(d);
  }
  linha("centro do novo campo de lugar", `${(somaPesoTempo / somaPeso / 1000).toFixed(2)} s em relação ao platô (antecipa)`);

  console.log("\nMarcação e captura: via fraca em t = 0, via forte em t = T, 8 h depois (seção 8.2 e exercício 6)");
  for (const T of [-60, 0, 30, 60, 120, 240]) {
    const c = criarPesoConsolidavel();
    potenciar(c, 1);
    for (let t = 0; t < 480; t += 0.5) {
      const proteinas = t >= T ? Math.exp(-(t - T) / 60) : 0;
      passoConsolidacao(c, proteinas, 0.5);
    }
    linha(`via forte em T = ${T} min`, `peso consolidado ${c.wLento.toFixed(2)} · rápido restante ${c.wRapido.toFixed(3)}`);
  }

  console.log("\nVárias escalas de tempo: memória em u₀ depois de uma potenciação (seções 8 e 18.4)");
  const tempos = [10, 100, 1000, 10000];
  for (const m of [1, 10]) {
    const u = new Array(m).fill(0);
    u[0] = 1;
    const lidos = [];
    for (let passo = 1; passo <= 20000; passo++) {
      passoCadeia(u, 0.5);
      if (tempos.includes(passo * 0.5)) lidos.push(u[0].toExponential(1));
    }
    linha(`${m} variável(eis), t = ${tempos.join(", ")}`, lidos.join(" · "));
  }

  console.log("\nInterruptor biestável (CaMKII): pulso de 10 unidades de tempo e depois nada (seção 5.3)");
  for (const estimulo of [0.05, 0.1, 0.15, 0.3]) {
    let x = 0;
    for (let t = 0; t < 300; t += 0.1) x = passoInterruptor(x, t < 10 ? estimulo : 0, 0.1);
    linha(`estímulo ${estimulo}`, `x = ${x.toFixed(2)} → ${x > 1 ? "ligado (memória)" : "desligado"}`);
  }

  console.log("\nInformação por sinapse (seção 12.1)");
  linha("26 tamanhos distinguíveis de espinha", `${bitsPorSinapse(26).toFixed(2)} bits`);
}

// ============================================================================
// 05 — Neuromodulação (neurociencia/05-neuromodulacao.md)
// Os moduladores não carregam conteúdo: mudam ganho, modo e plasticidade. Boa parte da matemática
// é a do aprendizado por reforço, com os moduladores no papel dos hiperparâmetros de Doya (9.4):
// dopamina ≈ δ (erro TD), serotonina ≈ γ (desconto), noradrenalina ≈ β (temperatura inversa)
// e acetilcolina ≈ α (taxa de aprendizado).
// ============================================================================

function somar(valores) {
  return valores.reduce((total, x) => total + x, 0);
}

function embaralhar(lista) {
  for (let i = lista.length - 1; i > 0; i--) {
    const j = Math.floor(aleatorio() * (i + 1));
    [lista[i], lista[j]] = [lista[j], lista[i]];
  }
  return lista;
}

// --- 3.2 Dopamina como erro de diferença temporal ----------------------------

// δ = r + γ·V(s') − V(s): rajada se δ > 0, nada se δ = 0, pausa se δ < 0
function erroTD(recompensa, valorAtual, valorProximo, gamma) {
  return recompensa + gamma * valorProximo - valorAtual;
}

// Um ensaio pista → espera → recompensa com TD(0). Os estados são os passos depois da pista
// (representação serial completa); antes da pista o valor é 0, porque a pista chega sem aviso.
// Atualiza V e devolve δ em cada passo, começando pela chegada da pista.
function ensaioTD(V, { recompensa, passoDaRecompensa, alfa = 0.1, gamma = 0.98 }) {
  const deltas = [erroTD(0, 0, V[0], gamma)];
  for (let s = 0; s < V.length; s++) {
    const delta = erroTD(s === passoDaRecompensa ? recompensa : 0, V[s], s + 1 < V.length ? V[s + 1] : 0, gamma);
    V[s] += alfa * delta;
    deltas.push(delta);
  }
  return deltas;
}

// Rescorla-Wagner: as pistas presentes dividem o mesmo erro, ΔV_i = α·(r − Σ V_presentes + extra).
// Daí o bloqueio de Kamin: se uma pista já prevê tudo, a nova não aprende. `dopaminaExtra` soma um
// erro artificial, como a estimulação (> 0, Steinberg et al., 2013) ou a inibição (< 0, Chang et al.,
// 2016) dos neurônios de dopamina. Devolve δ.
function rescorlaWagner(V, presentes, recompensa, { alfa = 0.2, dopaminaExtra = 0 } = {}) {
  const delta = recompensa - somar(presentes.map((i) => V[i])) + dopaminaExtra;
  for (const i of presentes) V[i] += alfa * delta;
  return delta;
}

// --- 3.3 Refinamentos ----------------------------------------------------------

// RL distribucional (Dabney et al., 2020): cada neurônio de dopamina tem o seu otimismo
// τ = α⁺/(α⁺ + α⁻). Com erros positivos pesando τ e negativos 1 − τ, o valor converge para o
// expectil τ da distribuição de recompensas, e a população inteira descreve a distribuição.
function passoDistribucional(valores, otimismos, recompensa, alfa = 0.02) {
  for (let i = 0; i < valores.length; i++) {
    const delta = recompensa - valores[i];
    valores[i] += alfa * (delta > 0 ? otimismos[i] : 1 - otimismos[i]) * delta;
  }
}

// Codificação adaptativa (Tobler et al., 2005): a resposta se ajusta à faixa de recompensas do contexto
function erroNormalizado(delta, faixa) {
  return delta / faixa;
}

// --- 3.4 Dopamina tônica: vigor e custo de oportunidade ---------------------------

// Niv et al. (2007): agir com latência τ custa C_v/τ (esforço) mais R̄·τ (o que se deixa de ganhar
// esperando, com R̄ a taxa média de recompensa = dopamina tônica). O mínimo é τ* = √(C_v/R̄).
function latenciaOtima(custoDeVigor, taxaMediaDeRecompensa) {
  return Math.sqrt(custoDeVigor / taxaMediaDeRecompensa);
}

// --- 11. Adição (Redish, 2004) ------------------------------------------------------

// A droga soma D ao erro e garante δ ≥ D: o erro nunca zera e o valor cresce sem limite
function erroTDComDroga(recompensa, valorAtual, valorProximo, gamma, droga) {
  return Math.max(erroTD(recompensa, valorAtual, valorProximo, gamma) + droga, droga);
}

// --- 5.2 e 9.4 Serotonina como paciência (γ) ------------------------------------------

function valorDescontado(recompensa, atraso, gamma) {
  return recompensa * gamma ** atraso;
}

// --- 4.3 e 9.1 Noradrenalina: ganho, temperatura e incerteza --------------------------

// Escolha softmax com temperatura inversa β: β alto → quase sempre o melhor (explotar);
// β baixo → escolhas espalhadas (explorar)
function softmax(valores, beta) {
  const maior = Math.max(...valores);
  const pesos = valores.map((v) => Math.exp(beta * (v - maior)));
  const total = somar(pesos);
  return pesos.map((p) => p / total);
}

function escolher(probabilidades) {
  let acumulado = 0;
  const u = aleatorio();
  for (let i = 0; i < probabilidades.length; i++) {
    acumulado += probabilidades[i];
    if (u < acumulado) return i;
  }
  return probabilidades.length - 1;
}

// U invertido (D1 no PFC, Yerkes-Dodson, ganho adaptativo do LC): o desempenho é máximo num nível
// intermediário do modulador. A forma gaussiana só descreve a curva.
function uInvertido(nivel, { otimo = 0.5, largura = 0.2 } = {}) {
  return Math.exp(-((nivel - otimo) ** 2) / (2 * largura ** 2));
}

// GANE (Mather et al., 2016): a noradrenalina amplifica o que já está ativo acima de um limiar e
// suprime o resto, aguçando a competição
function gane(ativacoes, noradrenalina, limiar = 0.5) {
  return ativacoes.map((x) => x * Math.exp(noradrenalina * (x - limiar)));
}

// Estimativa de uma média que pode saltar (Yu & Dayan, 2005), à maneira de um filtro de Kalman.
// Acetilcolina ≈ incerteza esperada: o ruído conhecido das observações. Noradrenalina ≈ incerteza
// inesperada: quando o erro é grande demais para esse ruído, "o mundo mudou", a incerteza da
// estimativa é reiniciada e a taxa de aprendizado salta. e = { media, variancia }. Devolve o ganho.
function passoEstimador(e, observacao, { varianciaRuido = 1, limiarSurpresa = 3, comReset = true } = {}) {
  const erro = observacao - e.media;
  if (comReset && Math.abs(erro) > limiarSurpresa * Math.sqrt(e.variancia + varianciaRuido)) e.variancia = 10 * varianciaRuido;
  const ganho = e.variancia / (e.variancia + varianciaRuido);
  e.media += ganho * erro;
  e.variancia *= 1 - ganho;
  return ganho;
}

// --- 9.1 e 9.2 Ganho e reconfiguração ----------------------------------------------------

// ACh e NA fecham correntes de K⁺ lentas, ou seja, tiram a adaptação do LIF do 02 e aumentam o ganho.
// nivel = 0 deixa a adaptação inteira; nivel = 1 a remove.
function lifModulado(nivel, base = { ...parametrosLIF, incrementoW: 3 }) {
  return { ...base, incrementoW: base.incrementoW * (1 - nivel) };
}

// Mesmo neurônio, outro modulador (Marder, 2012): o nível leva os parâmetros de Izhikevich de um
// tipo de disparo a outro, como um modulador que muda as correntes intrínsecas
function izhikevichModulado(nivel, de = tiposIzhikevich.regular, para = tiposIzhikevich.tagarela) {
  return Object.fromEntries(Object.keys(de).map((k) => [k, de[k] + nivel * (para[k] - de[k])]));
}

// --- 6.3 Hasselmo: a acetilcolina separa gravar de recordar ------------------------------

// Rede de Hopfield com unidades ±1. O estado vem da entrada externa somada à recorrente, e a
// acetilcolina alta suprime a recorrente (fatorRecorrente < 1).
function estadoDeHopfield(W, entrada, { forcaEntrada = 1, fatorRecorrente = 1, iteracoes = 8 } = {}) {
  let s = entrada.map((x) => (x >= 0 ? 1 : -1));
  for (let k = 0; k < iteracoes; k++) {
    s = W.map((pesos, i) => (forcaEntrada * entrada[i] + fatorRecorrente * produtoEscalar(pesos, s) >= 0 ? 1 : -1));
  }
  return s;
}

// Hebb sobre o estado que a rede realmente assumiu: W += taxa·s·sᵀ/N
function aprenderHopfield(W, s, taxa = 1) {
  const n = s.length;
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (i !== j) W[i][j] += (taxa * s[i] * s[j]) / n;
}

function sobreposicao(a, b) {
  return produtoEscalar(a, b) / a.length;
}

// --- 13.2 e 13.3 Surpresa e novidade que emergem da rede ------------------------------------

// População de erro: excitada pela entrada real e inibida pela predição. Uma metade sente o que
// chegou sem ser previsto, [x − p]₊, e a outra o que foi previsto e não veio, [p − x]₊.
function surpresa(entrada, predicao) {
  let total = 0;
  for (let i = 0; i < entrada.length; i++) total += Math.max(0, entrada[i] - predicao[i]) + Math.max(0, predicao[i] - entrada[i]);
  return total;
}

// Familiaridade: força média das conexões que o estímulo ativa. Novidade: um neurônio com atividade
// basal inibido pela familiaridade. Cada exposição fortalece essas conexões (LTP com limite suave).
function novidade(estimulo, pesos, { basal = 1, taxa = 0.3 } = {}) {
  const familiaridade = produtoEscalar(pesos, estimulo) / somar(estimulo);
  for (let i = 0; i < pesos.length; i++) pesos[i] += ltpSuave(pesos[i], taxa * estimulo[i], 1);
  return Math.max(0, basal - familiaridade);
}

// --- 7.1 Interruptor sono-vigília (Saper, Scammell & Lu, 2005) -------------------------------

// V: núcleos da vigília (LC, rafe, TMN); S: núcleo do sono (VLPO). Eles se inibem, e a inibição mútua
// dá biestabilidade. A pressão de sono h (adenosina) sobe acordado e cai dormindo. A orexina, ativa
// na vigília, reforça esse lado. Tempo em minutos. e = { vigilia, sono, pressao }.
const parametrosSonoVigilia = { tau: 5, inclinacao: 10, inibicao: 1, entradaVigilia: 0.2, entradaSono: -0.2, pesoPressao: 2, pesoOrexina: 0.7, tauSobe: 1180, tauDesce: 270, ruido: 0.08 };

function passoSonoVigilia(e, dt, orexina, p = parametrosSonoVigilia) {
  const alvoV = sigmoide(p.entradaVigilia + p.pesoOrexina * orexina * e.vigilia - p.inibicao * e.sono, 0, p.inclinacao);
  const alvoS = sigmoide(p.entradaSono + p.pesoPressao * e.pressao - p.inibicao * e.vigilia, 0, p.inclinacao);
  const ruido = () => p.ruido * Math.sqrt(dt / p.tau) * gaussiana();
  e.vigilia = Math.min(1, Math.max(0, e.vigilia + (dt / p.tau) * (alvoV - e.vigilia) + ruido()));
  e.sono = Math.min(1, Math.max(0, e.sono + (dt / p.tau) * (alvoS - e.sono) + ruido()));
  e.pressao += dt * (e.vigilia > 0.5 ? (1 - e.pressao) / p.tauSobe : -e.pressao / p.tauDesce);
}

// ============================================================================
// Simulações dos exercícios do 05
// ============================================================================

// Bandido de 4 braços cujas médias trocam de lugar a cada `trocaACada` tentativas (exercício 3).
// Fixo: β e α constantes. Adaptativo (13.5): a média móvel de |δ| faz o papel da noradrenalina
// tônica; erro alto → β baixo (explorar) e α alto (aprender rápido), erro baixo → β alto (focar).
function simularBandido({ adaptativo, tentativas = 20000, trocaACada = 200, ruido = 0.1 } = {}) {
  const medias = [0.2, 0.4, 0.6, 0.8];
  const Q = [0.5, 0.5, 0.5, 0.5];
  let erroMedio = 0.5;
  let total = 0;
  let melhores = 0;
  let melhoresLogoDepois = 0;
  for (let t = 0; t < tentativas; t++) {
    if (t % trocaACada === 0) embaralhar(medias);
    const beta = adaptativo ? 2 / Math.max(erroMedio, 0.02) : 10;
    const alfa = adaptativo ? Math.min(0.5, Math.max(0.05, 1.5 * erroMedio)) : 0.1;
    const braco = escolher(softmax(Q, beta));
    const recompensa = medias[braco] + ruido * gaussiana();
    const delta = recompensa - Q[braco];
    Q[braco] += alfa * delta;
    erroMedio += (Math.abs(delta) - erroMedio) / 20;
    total += recompensa;
    if (medias[braco] === 0.8) {
      melhores++;
      if (t % trocaACada < 50) melhoresLogoDepois++;
    }
  }
  const blocos = tentativas / trocaACada;
  return { recompensaMedia: total / tentativas, melhores: melhores / tentativas, logoDepois: melhoresLogoDepois / (50 * blocos) };
}

// Grava padrões sobrepostos (variações de um protótipo) e depois tenta recordá-los com pistas
// ruidosas (exercício 4). Com o interruptor: grava com a recorrência ×0,2 e plasticidade 1 e
// recorda com recorrência 1 e plasticidade 0. Sem: recorrência 1 e plasticidade 1 o tempo todo.
function simularHasselmo({ comInterruptor, n = 200, padroes = 5, variacao = 0.25, ruidoDaPista = 0.1 } = {}) {
  const variar = (x, p) => x.map((xi) => (aleatorio() < p ? -xi : xi));
  const prototipo = Array.from({ length: n }, () => (aleatorio() < 0.5 ? 1 : -1));
  const lista = Array.from({ length: padroes }, () => variar(prototipo, variacao));
  const W = Array.from({ length: n }, () => new Array(n).fill(0));
  let corrompidos = 0;
  for (const x of lista) {
    const s = estadoDeHopfield(W, x, { fatorRecorrente: comInterruptor ? 0.2 : 1 });
    if (sobreposicao(s, x) < 0.95) corrompidos++;
    aprenderHopfield(W, s);
  }
  let falhas = 0;
  for (const x of lista) {
    const s = estadoDeHopfield(W, variar(x, ruidoDaPista), { forcaEntrada: 0.5 });
    if (!comInterruptor) aprenderHopfield(W, s);
    if (sobreposicao(s, x) < 0.9) falhas++;
  }
  return { corrompidos, falhas };
}

// Recompensa distal (Izhikevich, 2007, simplificado; exercício 1). 100 neurônios de Izhikevich com
// entrada aleatória, passo de 1 ms. Cada sinapse excitatória guarda um traço de elegibilidade c que
// recebe a STDP e decai com τ = 1 s; a dopamina d decai com τ = 200 ms; a cada 10 ms,
// w += (0,002 + d)·c. Quando o neurônio `pre` da sinapse escolhida dispara e o `pos` dispara até
// 10 ms depois, chega dopamina 1–3 s mais tarde. O artigo usa 1000 neurônios, uma hora e 0,5 de
// dopamina por recompensa; aqui, com 100 neurônios e 15 minutos, cada recompensa libera 1. Mais
// dopamina aprende mais rápido, mas também reforça outras sinapses que por acaso estavam elegíveis.
// A taxa dos neurônios precisa ficar baixa (~1 Hz): com taxas altas, os pareamentos aleatórios do
// mesmo par (dominados por LTD) apagam o traço da coincidência premiada.
// Devolve, em alguns pontos, o peso da sinapse escolhida e o das outras.
function simularRecompensaDistal({ segundos = 900, n = 100, nExc = 80, saidasPorNeuronio = 10, entradaMedia = 0, dopaminaPorRecompensa = 1, pontos = 6 } = {}) {
  const wMax = 4;
  const neuronios = Array.from({ length: n }, (_, i) => {
    const tipo = i < nExc ? tiposIzhikevich.regular : tiposIzhikevich.rapido;
    return { ...criarIzhikevich(tipo), tipo, traco: 0, ultimoSpike: -Infinity };
  });
  const sinapses = [];
  for (let pre = 0; pre < n; pre++) {
    const alvos = new Set();
    while (alvos.size < saidasPorNeuronio) {
      const pos = Math.floor(aleatorio() * (pre < nExc ? n : nExc));
      if (pos !== pre) alvos.add(pos);
    }
    for (const pos of alvos) sinapses.push({ pre, pos, w: pre < nExc ? 1 : -1, c: 0 });
  }
  const saidas = neuronios.map(() => []);
  const entradas = neuronios.map(() => []);
  sinapses.forEach((s) => {
    saidas[s.pre].push(s);
    if (s.pre < nExc) entradas[s.pos].push(s);
  });
  const escolhida = sinapses.find((s) => s.pre < nExc && s.pos < nExc);
  const excitatorias = sinapses.filter((s) => s.pre < nExc);

  let dopamina = 0;
  let recompensas = [];
  let entregues = 0;
  const correntes = new Float64Array(n);
  const proximas = new Float64Array(n);
  const historico = [];
  const total = segundos * 1000;
  for (let t = 0; t < total; t++) {
    const disparos = [];
    for (let i = 0; i < n; i++) {
      const neuronio = neuronios[i];
      const corrente = correntes[i] + entradaMedia + 13 * (aleatorio() - 0.5);
      const disparou = passoIzhikevich(neuronio, neuronio.tipo, corrente, 0.5) || passoIzhikevich(neuronio, neuronio.tipo, corrente, 0.5);
      if (disparou) disparos.push(i);
    }
    correntes.set(proximas);
    proximas.fill(0);
    for (const i of disparos) {
      for (const s of entradas[i]) s.c += neuronios[s.pre].traco;
      for (const s of saidas[i]) {
        correntes[s.pos] += s.w;
        if (s.pre < nExc) s.c -= 1.5 * neuronios[s.pos].traco;
      }
      if (i === escolhida.pos && t - neuronios[escolhida.pre].ultimoSpike <= 10) recompensas.push(t + 1000 + aleatorio() * 2000);
    }
    for (const i of disparos) {
      neuronios[i].traco = 0.1;
      neuronios[i].ultimoSpike = t;
    }
    for (const neuronio of neuronios) neuronio.traco *= 0.95;

    dopamina *= 0.995;
    if (recompensas.length && recompensas[0] <= t) {
      dopamina += dopaminaPorRecompensa;
      entregues++;
      recompensas = recompensas.filter((r) => r > t);
    }
    if (t % 10 === 0) {
      for (const s of excitatorias) {
        s.w = limiteRigido(s.w + (0.002 + dopamina) * s.c, wMax);
        s.c *= 0.99;
      }
    }
    if ((t + 1) % (total / pontos) === 0) {
      const outras = excitatorias.filter((s) => s !== escolhida).map((s) => s.w);
      historico.push({ segundo: (t + 1) / 1000, escolhida: escolhida.w, mediaOutras: media(outras), outrasNoMaximo: outras.filter((w) => w >= 0.95 * wMax).length, totalOutras: outras.length, entregues });
    }
  }
  return historico;
}

// Três fatores com surpresa emergente (13.2 e exercício 5). Itens one-hot numa sequência; a predição
// do próximo item é a coluna de W do item atual. A surpresa vira o modulador M de uma regra
// Hebb × M com limite suave, e a normalização do 04 mantém a soma das predições de cada item ≤ 1.
// Devolve, por época, a surpresa média e o quanto os pesos mudaram.
function simularSurpresa(W, sequencia, epocas, eta = 0.5) {
  const nItens = W.length;
  const umQuente = (i) => Array.from({ length: nItens }, (_, k) => (k === i ? 1 : 0));
  const resultado = [];
  for (let epoca = 0; epoca < epocas; epoca++) {
    let surpresaTotal = 0;
    let mudanca = 0;
    for (let k = 1; k < sequencia.length; k++) {
      const anterior = sequencia[k - 1];
      const atual = umQuente(sequencia[k]);
      const predicao = W.map((linhaW) => linhaW[anterior]);
      const M = surpresa(atual, predicao) / 2;
      surpresaTotal += M;
      for (let j = 0; j < nItens; j++) {
        const dw = ltpSuave(W[j][anterior], eta * M * atual[j], 1);
        W[j][anterior] += dw;
        mudanca += Math.abs(dw);
      }
      const coluna = W.map((linhaW) => linhaW[anterior]);
      if (somar(coluna) > 1) {
        normalizarSoma(coluna, 1);
        coluna.forEach((w, j) => (W[j][anterior] = w));
      }
    }
    resultado.push({ surpresa: surpresaTotal / (sequencia.length - 1), mudanca });
  }
  return resultado;
}

// ============================================================================
// Exemplos do texto e exercícios da seção 14 do 05. Rode com: node index.js --05
// ============================================================================

function demonstracao05() {
  const f2 = (x) => x.toFixed(2);

  console.log("\nDopamina como erro TD: pista em t = 0, recompensa 1 s depois (seção 3.2 e exercício 2)");
  const V = new Array(13).fill(0);
  const ensaio = { recompensa: 1, passoDaRecompensa: 10 };
  for (let k = 1; k <= 500; k++) {
    const deltas = ensaioTD(V, ensaio);
    if ([1, 30, 100, 500].includes(k)) linha(`ensaio ${k}`, `δ na pista ${f2(deltas[0])} · δ na recompensa ${f2(deltas[11])}`);
  }
  const omissao = ensaioTD([...V], { ...ensaio, recompensa: 0 });
  linha("depois de aprender, recompensa omitida", `δ na pista ${f2(omissao[0])} · δ no momento esperado ${f2(omissao[11])}`);

  console.log("\nProbabilidade da recompensa (seção 3.3: Fiorillo, Tobler & Schultz, 2003)");
  for (const p of [0, 0.25, 0.5, 0.75, 1]) {
    const Vp = new Array(13).fill(0);
    for (let k = 0; k < 3000; k++) ensaioTD(Vp, { ...ensaio, recompensa: aleatorio() < p ? 1 : 0, alfa: 0.02 });
    const naPista = 0.98 * Vp[0];
    linha(`p = ${p}`, `δ na pista ${f2(naPista)} · recompensa entregue ${f2(1 - Vp[10])} · omitida ${f2(-Vp[10])}`);
  }

  console.log("\nBloqueio de Kamin e desbloqueio por dopamina (Rescorla-Wagner; seção 3.3)");
  const [A, B] = [0, 1];
  const casos = [
    ["sem fase 1: AB → recompensa", false, 0],
    ["A → recompensa, depois AB → recompensa", true, 0],
    ["o mesmo, com dopamina extra na fase 2", true, 0.5],
  ];
  for (const [nome, faseUm, dopaminaExtra] of casos) {
    const pistas = [0, 0];
    if (faseUm) for (let k = 0; k < 50; k++) rescorlaWagner(pistas, [A], 1);
    for (let k = 0; k < 50; k++) rescorlaWagner(pistas, [A, B], 1, { dopaminaExtra });
    linha(nome, `V(A) = ${f2(pistas[A])} · V(B) = ${f2(pistas[B])}`);
  }
  const aprendida = [1, 0];
  for (let k = 0; k < 20; k++) rescorlaWagner(aprendida, [A], 1, { dopaminaExtra: -0.5 });
  linha("A aprendida, dopamina inibida na recompensa", `V(A) cai para ${f2(aprendida[A])} mesmo com recompensa`);

  console.log("\nRL distribucional: recompensa 1 ou 9 com 50% cada (seção 3.3: Dabney et al., 2020)");
  const otimismos = [0.1, 0.3, 0.5, 0.7, 0.9];
  const bimodal = otimismos.map(() => 5);
  const fixa = otimismos.map(() => 5);
  for (let k = 0; k < 20000; k++) {
    passoDistribucional(bimodal, otimismos, aleatorio() < 0.5 ? 1 : 9);
    passoDistribucional(fixa, otimismos, 5);
  }
  linha("otimismo τ", otimismos.map((o) => o.toFixed(1).padStart(6)).join(""));
  linha("valor aprendido (recompensa 1 ou 9)", bimodal.map((v) => v.toFixed(2).padStart(6)).join(""));
  linha("expectil teórico, 8τ + 1", otimismos.map((o) => (8 * o + 1).toFixed(2).padStart(6)).join(""));
  linha("valor aprendido (recompensa sempre 5)", fixa.map((v) => v.toFixed(2).padStart(6)).join(""));

  console.log("\nCodificação adaptativa: a maior recompensa de cada contexto (seção 3.3: Tobler et al., 2005)");
  linha("contexto 0–0,1: recompensa 0,1 (esperada 0,05)", `δ = ${f2(0.05)} → normalizado ${f2(erroNormalizado(0.05, 0.1))}`);
  linha("contexto 0–1: recompensa 1 (esperada 0,5)", `δ = ${f2(0.5)} → normalizado ${f2(erroNormalizado(0.5, 1))}`);

  console.log("\nDopamina tônica e vigor: latência ótima τ* = √(C_v/R̄), com C_v = 1 (seção 3.4: Niv et al., 2007)");
  for (const taxa of [0.1, 0.5, 1, 4]) {
    let melhor = 0;
    let menorCusto = Infinity;
    for (let tau = 0.01; tau < 20; tau += 0.001) {
      const custo = 1 / tau + taxa * tau;
      if (custo < menorCusto) [menorCusto, melhor] = [custo, tau];
    }
    linha(`R̄ = ${taxa}`, `τ* = ${f2(latenciaOtima(1, taxa))} (mínimo numérico ${f2(melhor)})`);
  }

  console.log("\nAdição: δ = max(r + γV' − V + D, D) com D = 0,2 (seção 11: Redish, 2004)");
  for (const [nome, droga] of [["recompensa natural", 0], ["droga", 0.2]]) {
    let valor = 0;
    const lidos = [];
    for (let k = 1; k <= 1000; k++) {
      valor += 0.1 * erroTDComDroga(1, valor, 0, 0, droga);
      if ([10, 100, 1000].includes(k)) lidos.push(f2(valor));
    }
    linha(`${nome}: V após 10, 100, 1000 ensaios`, lidos.join(" → "));
  }

  console.log("\nSerotonina como paciência: 1 agora × 3 daqui a 20 passos (seções 5.2 e 9.4)");
  for (const gamma of [0.9, 0.94, 0.95, 0.99]) {
    const agora = valorDescontado(1, 1, gamma);
    const depois = valorDescontado(3, 20, gamma);
    linha(`γ = ${gamma}`, `agora ${f2(agora)} · esperar ${f2(depois)} → ${depois > agora ? "espera" : "pega agora"}`);
  }

  console.log("\nNoradrenalina como temperatura: softmax de Q = [0,2 0,4 0,6 0,8] (seção 9.1)");
  for (const beta of [1, 5, 20]) linha(`β = ${beta}`, softmax([0.2, 0.4, 0.6, 0.8], beta).map(f2).join("  "));

  console.log("\nBandido de 4 braços que muda a cada 200 tentativas (seção 13.5 e exercício 3)");
  for (const [nome, adaptativo] of [["temperatura e taxa fixas (β = 10, α = 0,1)", false], ["β e α pela média de |δ| (noradrenalina)", true]]) {
    const r = simularBandido({ adaptativo });
    linha(nome, `recompensa média ${f2(r.recompensaMedia)} · melhor braço ${(100 * r.melhores).toFixed(0)}% · nas 50 após cada troca ${(100 * r.logoDepois).toFixed(0)}%`);
  }

  console.log("\n\"O mundo mudou\": média que salta entre 0 e 5 a cada 100 observações, ruído σ = 1 (seção 4.5)");
  const estrategias = [
    ["α fixo = 0,05", (e, x) => (e.media += 0.05 * (x - e.media))],
    ["α fixo = 0,5", (e, x) => (e.media += 0.5 * (x - e.media))],
    ["Kalman sem reset (só ACh)", (e, x) => passoEstimador(e, x, { comReset: false })],
    ["Kalman com reset (ACh + NA)", (e, x) => passoEstimador(e, x)],
  ];
  for (const [nome, passo] of estrategias) {
    const e = { media: 0, variancia: 10 };
    let erro = 0;
    for (let t = 0; t < 2000; t++) {
      const verdadeira = Math.floor(t / 100) % 2 === 0 ? 0 : 5;
      passo(e, verdadeira + gaussiana());
      erro += Math.abs(e.media - verdadeira);
    }
    linha(nome, `erro médio ${f2(erro / 2000)}`);
  }

  console.log("\nGANE: a noradrenalina aguça a competição entre ativações [0,2 0,5 0,9] (seção 4.6)");
  for (const na of [0, 1, 3]) linha(`NA = ${na}`, gane([0.2, 0.5, 0.9], na).map(f2).join("  "));

  console.log("\nU invertido: desempenho × nível do modulador (seções 3.4 e 4.3)");
  linha("nível", [0, 0.25, 0.5, 0.75, 1].map((x) => x.toFixed(2).padStart(6)).join(""));
  linha("desempenho", [0, 0.25, 0.5, 0.75, 1].map((x) => uInvertido(x).toFixed(2).padStart(6)).join(""));

  console.log("\nGanho: ACh/NA tiram a adaptação de um LIF (seção 9.1)");
  for (const nivel of [0, 0.5, 1]) {
    const [f1, f2b] = curvaFI(modeloLIF(lifModulado(nivel)), [0.2, 0.4]);
    linha(`modulador ${nivel}`, `f-I: ${hz(f1)} em 0,2 nA, ${hz(f2b)} em 0,4 nA · inclinação ${(f2b - f1) / 0.2 | 0} Hz/nA`);
  }

  console.log("\nMarder: o mesmo neurônio e a mesma entrada (I = 10), outro modulador (seção 1.1)");
  for (const nivel of [0, 0.5, 1]) {
    const tempos = tempoDosSpikes(modeloIzhikevich(izhikevichModulado(nivel)), (t) => (t >= 20 ? 10 : 0), 320, 0.1);
    linha(`nível ${nivel} (${tempos.length} spikes)`, `intervalos: ${intervalos(tempos).slice(0, 8).map((x) => x.toFixed(1)).join(", ")} ms`);
  }

  console.log("\nHasselmo: 5 padrões sobrepostos numa rede de Hopfield de 200 unidades, média de 20 redes (seção 6.3 e exercício 4)");
  for (const [nome, comInterruptor] of [["sem interruptor", false], ["com interruptor de ACh", true]]) {
    const repeticoes = 20;
    let corrompidos = 0;
    let falhas = 0;
    for (let k = 0; k < repeticoes; k++) {
      const r = simularHasselmo({ comInterruptor });
      corrompidos += r.corrompidos;
      falhas += r.falhas;
    }
    linha(nome, `gravados corrompidos ${(corrompidos / repeticoes).toFixed(1)} de 5 · recordações erradas ${(falhas / repeticoes).toFixed(1)} de 5`);
  }

  console.log("\nRecompensa distal: só a sinapse que \"causou\" a dopamina cresce (seção 10 e exercício 1)");
  for (const ponto of simularRecompensaDistal()) {
    linha(
      `t = ${ponto.segundo} s (${ponto.entregues} recompensas)`,
      `sinapse escolhida ${f2(ponto.escolhida)} · média das outras ${f2(ponto.mediaOutras)} · outras no máximo ${ponto.outrasNoMaximo} de ${ponto.totalOutras}`,
    );
  }

  console.log("\nSurpresa emergente como terceiro fator: sequência A B C D E F (seção 13.2 e exercício 5)");
  const W = Array.from({ length: 7 }, () => new Array(7).fill(0));
  const mostrar = [1, 2, 3, 5, 10, 20];
  const antes = simularSurpresa(W, [0, 1, 2, 3, 4, 5], 20);
  const depois = simularSurpresa(W, [0, 1, 2, 6, 4, 5], 20); // C passa a ser seguido por G
  for (const [rotulo, resultado] of [["", antes], [" depois de C → G", depois]]) {
    for (const epoca of mostrar) {
      const r = resultado[epoca - 1];
      linha(`época ${epoca}${rotulo}`, `surpresa ${f2(r.surpresa)} · mudança nos pesos ${f2(r.mudanca)}`);
    }
  }

  console.log("\nNovidade = familiaridade baixa (seção 13.3)");
  const pesosFamiliaridade = new Array(8).fill(0);
  const estimuloA = [1, 1, 1, 0, 0, 0, 0, 0];
  const estimuloB = [0, 0, 0, 0, 0, 1, 1, 1];
  const exposicoes = Array.from({ length: 5 }, () => f2(novidade(estimuloA, pesosFamiliaridade)));
  linha("estímulo A, 5 exposições", exposicoes.join(" → "));
  linha("estímulo B, primeira vez", f2(novidade(estimuloB, pesosFamiliaridade)));

  console.log("\nInterruptor sono-vigília em 5 dias (seção 7.1: Saper et al., 2005)");
  for (const [nome, orexina] of [["com orexina", 1], ["sem orexina (narcolepsia)", 0]]) {
    const e = { vigilia: 1, sono: 0, pressao: 0.1 };
    let acordado = true;
    let inicio = 0;
    const episodios = [];
    const dt = 0.5;
    for (let t = 0; t < 5 * 24 * 60; t += dt) {
      passoSonoVigilia(e, dt, orexina);
      if (e.vigilia > 0.5 !== acordado) {
        if (acordado) episodios.push(t - inicio);
        acordado = !acordado;
        inicio = t;
      }
    }
    linha(nome, `${(episodios.length / 5).toFixed(1)} adormecimentos por dia · vigília média ${(media(episodios) / 60).toFixed(1)} h · mais longa ${(Math.max(...episodios) / 60).toFixed(1)} h`);
  }
}

// ============================================================================
// O cérebro: uma rede que junta 01–05
//   neurônios de Izhikevich (02), excitatórios entre regular e tagarela, inibitórios rápidos
//   princípio de Dale (03 §16.5): cada neurônio é só excitatório ou só inibitório
//   sinapses por condutância (01 §14.2): AMPA, NMDA com bloqueio de Mg²⁺ e GABA-A com E_Cl de Nernst
//   depressão de curto prazo de Tsodyks-Markram e pesos iniciais lognormais (03)
//   entrada de fundo Poisson (03); STDP de tripletos, escalonamento sináptico e iSTDP (04).
//   Tripletos e não pares porque a STDP em pares com dominância de LTD enfraquece um grupo que
//   dispara junto em alta frequência (a ressalva da seção 9.5); os tripletos dão LTP nesse caso.
//   A LTD tem limite suave (proporcional a w): com LTD aditiva, os pesos fora de um grupo ativo
//   iam todos a zero em atividade espontânea, e o escalonamento multiplicativo não os segurava.
//   Neuromodulação (05), com níveis tônicos dados pelo estado (vigília, NREM, REM; seção 8):
//     acetilcolina: ganho na entrada externa, supressão da recorrência E→E e plasticidade (Hasselmo)
//     noradrenalina: tira a adaptação dos neurônios, ou seja, aumenta o ganho (9.1)
//     três fatores (10): a STDP vai para um traço de elegibilidade, e o peso só muda com o fator M,
//     que sobe com ACh, dopamina fásica e noradrenalina fásica. Acordado e sem eventos, M = 1 e o
//     resultado é o mesmo de aplicar a STDP direto. Recompensa e surpresa são eventos do
//     ambiente, que soltam dopamina e noradrenalina fásicas.
//   A rede foi calibrada acordada (ACh 1, NA 0,5), então nesses níveis todos os fatores valem 1.
// ============================================================================

// Níveis tônicos de cada estado cerebral (seção 8 do 05)
const estadosCerebrais = {
  vigilia: { acetilcolina: 1, noradrenalina: 0.5 },
  nrem: { acetilcolina: 0.1, noradrenalina: 0.1 },
  rem: { acetilcolina: 1, noradrenalina: 0 },
};

// Quanto cada modulador muda cada efeito (ver atualizarModuladores)
const efeitosDosModuladores = {
  ganhoExternoSemACh: 0.25, // fração da entrada externa que some sem ACh (nicotínicos)
  recorrenciaSemACh: 0.6, // quanto a recorrência E→E cresce sem ACh (muscarínicos pré-sinápticos)
  adaptacaoPorNA: 0.6, // quanto cada unidade de NA acima de 0,5 tira da adaptação
  plasticidadeSemACh: 0.8, // quanto do fator M depende da ACh
  dopaminaNaPlasticidade: 6,
  noradrenalinaNaPlasticidade: 1,
};

const configuracaoCerebro = {
  nExc: 100,
  nInib: 25,
  pConexao: 0.2,
  dt: 0.25, // ms
  entradaFundo: 800, // Hz: spikes de fundo que cada neurônio recebe (soma de muitas entradas)
  gFundo: 0.012, // condutância de cada spike de fundo
  razaoNMDA: 0.1, // g_NMDA / g_AMPA nas sinapses excitatórias
  stp: true, // depressão de curto prazo
  stdp: true,
  escalonamento: true,
  istdp: true,
  estado: "vigilia", // uma chave de estadosCerebrais
  // Opções do experimento --conectoma
  pesosIniciaisIguais: false, // E→E começam todos na mediana, sem lognormal
  regraSTDP: "tripletos", // ou "pares"
  gruposCorrelacionados: [], // listas de neurônios; cada lista recebe spikes de uma fonte comum
  taxaCorrelacionada: 0, // Hz de cada fonte comum
  // Rajadas por grupo: { taxaHz, duracao (ms), entradaHz }. Cada grupo entra em rajada ao acaso
  // (taxaHz por segundo); durante a rajada, cada neurônio do grupo recebe entrada extra própria
  // de entradaHz. Os neurônios ficam com taxas correlacionadas, sem spikes em comum.
  rajadasDeGrupo: null,
  // Elegibilidade exata e preguiçosa (ver sincronizarSinapse): bem mais rápida em redes grandes,
  // com números levemente diferentes do Euler de 1 ms, por isso desligada fora do experimento
  elegibilidadeExata: false,
  // Plasticidade estrutural: { intervalo (ms), fracao, idadeMinima (ms), pesoInicial (fração da
  // mediana) } ou null (ver religar)
  plasticidadeEstrutural: null,
  // Ruído multiplicativo nos pesos E→E, independente de atividade (por √s): a cada 100 ms,
  // ln w recebe um passo gaussiano, como as flutuações espontâneas do tamanho das espinhas
  ruidoMultiplicativo: 0,
  // false: as sinapses E→E não entregam nada (os pesos continuam lá; E→I, I→E e I→I seguem)
  recorrenciaEE: true,
  // Excitatórios "izhikevich" ou "adex" (o AdEx da regra de Clopath, parametrosAdExClopath). As
  // condutâncias dão a corrente nas unidades do Izhikevich; o AdEx recebe ganhoAdEx vezes ela (pA).
  modeloExcitatorio: "izhikevich",
  ganhoAdEx: 281,
  // false: não guarda a voltagem do neurônio selecionado a cada passo (é para a visualização, que
  // esvazia o registro 30 vezes por segundo; numa simulação longa sem visualização ele só cresce)
  registrarTraco: true,
  // Bits de cada peso: 64 (double) ou 16 e 8 (inteiros com arredondamento estocástico; ver gravarPeso)
  bitsDosPesos: 64,
  // true: as E→I e as I→I, que não aprendem, saem de um hash de sementeDaFiacao a cada spike em vez
  // de ficarem guardadas (ver saidasProcedurais)
  conexoesProcedurais: false,
  sementeDaFiacao: 1,
  // true (modo --integrado): os níveis de acetilcolina, noradrenalina e dopamina vêm de fora, em
  // moduladoresRecebidos, produzidos pelas regiões; o estado e os botões deixam de valer
  moduladoresDeFora: false,
};

// Os efeitos dos níveis m = { acetilcolina, noradrenalina, noradrenalinaFasica, dopaminaFasica }:
// ganho na entrada externa, fator da recorrência E→E, adaptação e o fator M da plasticidade
function calcularEfeitos(m, efeitos, k = efeitosDosModuladores) {
  const semACh = 1 - m.acetilcolina;
  efeitos.ganhoExterno = 1 - k.ganhoExternoSemACh * semACh;
  efeitos.recorrencia = 1 + k.recorrenciaSemACh * semACh;
  efeitos.adaptacao = Math.max(0.2, 1 - k.adaptacaoPorNA * (m.noradrenalina + m.noradrenalinaFasica - 0.5));
  efeitos.plasticidade =
    1 - k.plasticidadeSemACh * semACh + k.dopaminaNaPlasticidade * m.dopaminaFasica + k.noradrenalinaNaPlasticidade * m.noradrenalinaFasica;
  return efeitos;
}

// Peso inicial (mediana da lognormal) e máximo por tipo de conexão: pré → pós. A LTP E→E é medida
// em frações de w_max; com `escalaLTP` (opcional) ela usa essa escala, e w_max vira só o teto.
const pesosPorTipo = {
  EE: { mediana: 0.02, wMax: 0.08 },
  EI: { mediana: 0.03, wMax: 0.12 },
  IE: { mediana: 0.05, wMax: 0.3 },
  II: { mediana: 0.05, wMax: 0.3 },
};

const plasticidadeCerebro = {
  tm: { U: 0.3, tauRec: 400 }, // sinapses excitatórias depressoras
  tripletos: parametrosTripletos, // STDP E→E; Δw em frações de w_max
  tauTraco: 20, // traço do iSTDP
  taxaAlvo: 5, // Hz, para o escalonamento e o iSTDP
  epsilon: 0.0005, // escalonamento a cada 100 ms (acelerado: no cérebro leva horas)
  tauTaxa: 2000, // janela da taxa média de cada neurônio
  etaInib: 0.0005,
  tauElegibilidade: 1000, // ms
  tauTonico: 2000, // ms para os níveis tônicos chegarem aos do novo estado
  tauFasico: 200, // ms de decaimento da dopamina e da noradrenalina fásicas
  // Regra de Clopath na rede (regraSTDP "clopath"): a da seção 9.5 com dois detalhes da
  // implementação de referência (o aeif_psc_delta_clopath do NEST): ū₋ e ū₊ entram na regra com
  // `atraso` ms de atraso, e a LTD é homeostática, A_LTD·ū̄²/u_ref², com ū̄ a despolarização média
  // (ū₋ − E_L filtrada em tauMedia ms) e u_ref² = 60 mV². Δw em frações de w_max, como nos tripletos.
  clopath: { ...parametrosClopath, atraso: 4, uRef2: 60, tauMedia: 500, eL: -70.6 },
};

// AdEx da regra de Clopath (os padrões do aeif_psc_delta_clopath do NEST): depois de cada spike a
// voltagem fica tTravado ms em vPico e volta a vReset; uma corrente despolarizante z (pós-potencial)
// salta para iSp e decai com τ_z, e o limiar V_T salta para vTMax e volta a vTRepouso com τ_VT.
// Sem o pós-potencial, a regra de Clopath com atraso não dá LTP em alta frequência (ver
// avaliarNeuronioDeClopath).
const parametrosAdExClopath = {
  c: 281, gL: 30, eL: -70.6, deltaT: 2, tauW: 144, a: 4, b: 80.5,
  vReset: -60, vPico: 33, tTravado: 2, iSp: 400, tauZ: 40, vTMax: 30.4, vTRepouso: -50.4, tauVT: 50,
};

function criarAdExClopath(p = parametrosAdExClopath) {
  return { v: p.eL, w: 0, z: 0, vT: p.vTRepouso, travado: 0 };
}

// Devolve true no passo em que o spike começa. No passo do spike o v pode passar muito de vPico (a
// exponencial explode), então ele é travado em vPico antes de entrar na adaptação. O spike é
// detectado em vDisparo, se houver (o V_peak do NEST), e senão no próprio vPico.
function passoAdExClopath(s, p, corrente, dt) {
  let disparou = false;
  if (s.travado > 0) {
    s.travado -= dt;
    if (s.travado <= 1e-9) s.v = p.vReset;
  } else {
    const inicioDoSpike = p.gL * p.deltaT * Math.exp(Math.min(20, (s.v - s.vT) / p.deltaT));
    s.v += (dt / p.c) * (-p.gL * (s.v - p.eL) + inicioDoSpike - s.w + s.z + corrente);
    if (s.v >= (p.vDisparo ?? p.vPico)) {
      s.v = p.vPico;
      disparou = true;
    }
  }
  s.w += (dt / p.tauW) * (p.a * (s.v - p.eL) - s.w);
  s.z -= (dt / p.tauZ) * s.z;
  s.vT += (dt / p.tauVT) * (p.vTRepouso - s.vT);
  if (disparou) Object.assign(s, { travado: p.tTravado, w: s.w + p.b, z: p.iSp, vT: p.vTMax });
  return disparou;
}

// A regra em pares é a de tripletos com o traço lento o2 trocado pelo seu valor médio na taxa-alvo
// (ρ₀·τ_y): as duas têm o mesmo equilíbrio a 5 Hz, mas só a de tripletos depende da frequência.
plasticidadeCerebro.aParesMais = parametrosTripletos.a3Mais * (plasticidadeCerebro.taxaAlvo / 1000) * parametrosTripletos.tauY;

// Tipos de sinapse (pré → pós); sinapse.tipo guarda o índice
const TIPOS_DE_SINAPSE = ["EE", "EI", "IE", "II"];
const SINAPSE_EE = 0;
const SINAPSE_EI = 1;
const SINAPSE_IE = 2;
const SINAPSE_II = 3;

// Listas de ids de sinapse, uma por neurônio, num único Int32Array (formato CSR): a lista i ocupa
// ids[inicio[i] ... inicio[i] + quantas[i]) e tem vagas livres até inicio[i + 1], para a religação
// pôr sinapses novas sem realocar. Se uma lista enche, a tabela é refeita com mais vagas nela.
class ListasDeIds {
  constructor(listas, folga = 0.25) {
    this.folga = folga;
    this.montar(listas);
  }

  montar(listas, aumentar = -1) {
    const n = listas.length;
    this.inicio = new Int32Array(n + 1);
    listas.forEach((lista, i) => {
      const vagas = lista.length + Math.max(4, Math.ceil(this.folga * lista.length)) + (i === aumentar ? lista.length + 4 : 0);
      this.inicio[i + 1] = this.inicio[i] + vagas;
    });
    this.quantas = Int32Array.from(listas, (lista) => lista.length);
    this.ids = new Int32Array(this.inicio[n]);
    listas.forEach((lista, i) => this.ids.set(lista, this.inicio[i]));
  }

  lista(i) {
    return this.ids.subarray(this.inicio[i], this.inicio[i] + this.quantas[i]);
  }

  // Tira o id da lista i mantendo a ordem dos outros (como splice)
  tirar(i, id) {
    const fim = this.inicio[i] + this.quantas[i];
    let p = this.inicio[i];
    while (this.ids[p] !== id) p++;
    this.ids.copyWithin(p, p + 1, fim);
    this.quantas[i]--;
  }

  // Põe o id no fim da lista i (como push)
  por(i, id) {
    if (this.inicio[i] + this.quantas[i] === this.inicio[i + 1]) {
      this.montar(Array.from(this.quantas, (_, k) => Array.from(this.lista(k))), i);
    }
    this.ids[this.inicio[i] + this.quantas[i]++] = id;
  }
}

class Cerebro {
  // opcoes: chaves de configuracaoCerebro e, para redes de outro tamanho, `pesos` (no formato de
  // pesosPorTipo) e `plasticidade` (chaves de plasticidadeCerebro a trocar)
  constructor({ pesos = pesosPorTipo, plasticidade = {}, ...opcoes } = {}) {
    this.config = { ...configuracaoCerebro, ...opcoes };
    this.pesos = pesos;
    this.plasticidade = { ...plasticidadeCerebro, ...plasticidade };
    const { nExc, nInib, pConexao, dt } = this.config;
    this.n = nExc + nInib;
    this.t = 0;
    this.eGaba = potencialDeNernst(ions.Cl); // ≈ −72 mV
    this.grupo = Array.from({ length: 20 }, (_, i) => i); // excitatórios que o botão "estimular grupo" ativa
    this.selecionado = 0;
    this.estimulos = [];
    this.registro = { spikes: [], traco: [] };
    this.neuronios = Array.from({ length: this.n }, (_, i) => this.criarNeuronio(i));
    this.criarSinapses(pConexao);
    this.moduladores = { ...estadosCerebrais[this.config.estado], dopaminaFasica: 0, noradrenalinaFasica: 0 };
    this.moduladoresRecebidos = { ...this.moduladores };
    this.efeitosDosModuladores = efeitosDosModuladores; // trocável nos testes de causa do --integrado
    this.efeitos = { ganhoExterno: 1, recorrencia: 1, adaptacao: 1, plasticidade: 1 };
    this.plasticidadeSincronizada = 1; // o M com que as sinapses foram sincronizadas (modo exato)
    const { tripletos, tauTraco, tauTaxa, tauTonico, tauFasico } = this.plasticidade;
    this.decaimento = {
      tonico: Math.exp(-dt / tauTonico),
      fasico: Math.exp(-dt / tauFasico),
      ampa: Math.exp(-dt / tausSinapticos.ampa),
      nmda: Math.exp(-dt / tausSinapticos.nmda),
      gaba: Math.exp(-dt / tausSinapticos.gabaA),
      traco: Math.exp(-dt / tauTraco),
      r1: Math.exp(-dt / tripletos.tauMais),
      o1: Math.exp(-dt / tripletos.tauMenos),
      o2: Math.exp(-dt / tripletos.tauY),
      taxa: Math.exp(-dt / tauTaxa),
    };
    if (this.config.regraSTDP === "clopath") this.criarClopath();
  }

  // Estado da regra de Clopath, por excitatório: ū₋, ū₊, ū̄, o traço pré x̄ e um anel com os ū₋ e
  // ū₊ dos últimos `atraso` ms (a regra usa os valores atrasados, guardados em uMenosAtrasado e
  // uMaisAtrasado). Ela lê a forma da voltagem, por isso pede os excitatórios AdEx.
  criarClopath() {
    if (this.config.modeloExcitatorio !== "adex") throw new Error('a regra de Clopath pede modeloExcitatorio: "adex"');
    const { nExc, dt } = this.config;
    const p = this.plasticidade.clopath;
    const comprimento = Math.round(p.atraso / dt);
    const cheio = (valor, n = nExc) => new Float64Array(n).fill(valor);
    this.clopath = {
      uMenos: cheio(p.eL),
      uMais: cheio(p.eL),
      media: cheio(Math.sqrt(p.uRef2)), // ū̄ começa na referência: LTD sem ganho nem perda
      xBarra: cheio(0),
      uMenosAtrasado: cheio(p.eL),
      uMaisAtrasado: cheio(p.eL),
      anelMenos: cheio(p.eL, nExc * comprimento),
      anelMais: cheio(p.eL, nExc * comprimento),
      comprimento,
      posicao: 0,
      decaiMenos: Math.exp(-dt / p.tauMenos),
      decaiMais: Math.exp(-dt / p.tauMais),
      decaiMedia: Math.exp(-dt / p.tauMedia),
      decaiX: Math.exp(-dt / p.tauX),
    };
  }

  // Um passo da regra de Clopath, depois de integrar as voltagens. LTP contínua em cada entrada E→E
  // dos neurônios com u > θ₊ (na prática, durante o spike travado em 33 mV):
  //   dw/dt = A_LTP·x̄_pré·[u − θ₊]₊·[ū₊ − θ₋]₊ (ū₊ atrasado)
  // A LTD fica em disparar, no spike pré. Depois os filtros andam com a voltagem deste passo.
  passoClopath() {
    const c = this.clopath;
    const p = this.plasticidade.clopath;
    const { nExc, dt, stdp, elegibilidadeExata } = this.config;
    const escala = this.pesos.EE.escalaLTP ?? this.pesos.EE.wMax;
    const s = this.sinapse;
    const { inicio, quantas, ids } = this.entradasEE;
    for (let j = 0; j < nExc; j++) {
      const u = this.neuronios[j].v;
      const k = j * c.comprimento + c.posicao;
      c.uMenosAtrasado[j] = c.anelMenos[k];
      c.uMaisAtrasado[j] = c.anelMais[k];
      if (stdp && u > p.thetaMais && c.uMaisAtrasado[j] > p.thetaMenos) {
        const fator = escala * dt * p.aLTP * (u - p.thetaMais) * (c.uMaisAtrasado[j] - p.thetaMenos);
        for (let q = inicio[j], fim = q + quantas[j]; q < fim; q++) {
          const id = ids[q];
          if (c.xBarra[s.pre[id]] === 0) continue;
          if (elegibilidadeExata) this.sincronizarSinapse(id);
          s.elegibilidade[id] += fator * c.xBarra[s.pre[id]];
        }
      }
      c.anelMenos[k] = c.uMenos[j];
      c.anelMais[k] = c.uMais[j];
      c.uMenos[j] = u + (c.uMenos[j] - u) * c.decaiMenos;
      c.uMais[j] = u + (c.uMais[j] - u) * c.decaiMais;
      const despolarizacao = c.uMenos[j] - p.eL;
      c.media[j] = despolarizacao + (c.media[j] - despolarizacao) * c.decaiMedia;
      c.xBarra[j] *= c.decaiX;
      if (c.xBarra[j] < 1e-12) c.xBarra[j] = 0;
    }
    c.posicao = (c.posicao + 1) % c.comprimento;
  }

  ehExcitatorio(i) {
    return i < this.config.nExc;
  }

  // Parâmetros com variação, como na rede de Izhikevich (2003)
  criarNeuronio(i) {
    const r = aleatorio();
    const izh = this.ehExcitatorio(i)
      ? { a: 0.02, b: 0.2, c: -65 + 15 * r * r, d: 8 - 6 * r * r }
      : { a: 0.02 + 0.08 * r, b: 0.25 - 0.05 * r, c: -65, d: 2 };
    // traco: iSTDP; r1, o1, o2: tripletos (o r2 não entra porque A3₋ = 0)
    const adex = this.ehExcitatorio(i) && this.config.modeloExcitatorio === "adex";
    const membrana = adex ? { ...criarAdExClopath(), adex } : criarIzhikevich(izh);
    // tm: o estado de Tsodyks-Markram das saídas excitatórias, que só depende dos spikes deste neurônio
    const tm = this.ehExcitatorio(i) ? criarSinapseTM(this.plasticidade.tm) : null;
    return { ...membrana, izh, tm, gAmpa: 0, gNmda: 0, gGaba: 0, traco: 0, r1: 0, o1: 0, o2: 0, taxa: this.plasticidade.taxaAlvo };
  }

  // As sinapses ficam em arrays tipados, uma posição por sinapse (o id k), em this.sinapse:
  //   pre, pos, tipo (o índice em TIPOS_DE_SINAPSE), w, elegibilidade, tElegibilidade (a última
  //   sincronização, no modo exato) e nascimento (plasticidade estrutural)
  // As saídas, as entradas e as entradas E→E de cada neurônio são listas de ids (ListasDeIds), e
  // idsEE guarda as sinapses E→E na ordem em que foram criadas. Os ids nunca mudam: a religação
  // reaproveita o id de cada sinapse podada. A depressão de curto prazo fica no neurônio pré (tm),
  // porque só depende dos spikes dele. Com conexoesProcedurais, as E→I e as I→I (que não aprendem)
  // não ficam guardadas: saem de um hash a cada spike (ver saidasProcedurais).
  criarSinapses(pConexao) {
    const criadas = { pre: [], pos: [], tipo: [], w: [] };
    const procedural = this.config.conexoesProcedurais;
    for (let pre = 0; pre < this.n; pre++) {
      for (let pos = 0; pos < this.n; pos++) {
        if (pre === pos || aleatorio() >= pConexao) continue;
        const tipo = (this.ehExcitatorio(pre) ? 0 : 2) + (this.ehExcitatorio(pos) ? 0 : 1);
        const { mediana, wMax } = this.pesos[TIPOS_DE_SINAPSE[tipo]];
        const iguais = this.config.pesosIniciaisIguais && tipo === SINAPSE_EE;
        const w = iguais ? mediana : Math.min(wMax, amostraLognormal(mediana, 0.5));
        // a procedural é sorteada mesmo assim, para o gerador seguir a mesma sequência
        if (procedural && (tipo === SINAPSE_EI || tipo === SINAPSE_II)) continue;
        criadas.pre.push(pre);
        criadas.pos.push(pos);
        criadas.tipo.push(tipo);
        criadas.w.push(w);
      }
    }
    const total = criadas.pre.length;
    this.nSinapses = total;
    this.nProcedurais = 0;
    if (procedural) for (let i = 0; i < this.n; i++) this.saidasProcedurais(i, () => this.nProcedurais++);
    this.sinapse = {
      pre: Int32Array.from(criadas.pre),
      pos: Int32Array.from(criadas.pos),
      tipo: Uint8Array.from(criadas.tipo),
      w: Float64Array.from(criadas.w),
      elegibilidade: new Float64Array(total),
      tElegibilidade: new Float64Array(total),
      nascimento: new Float64Array(total),
    };
    this.wMaxDoTipo = Float64Array.from(TIPOS_DE_SINAPSE, (tipo) => this.pesos[tipo].wMax);
    this.passoDoPeso = null;
    const { bitsDosPesos: bits } = this.config;
    if (bits !== 64) {
      if (bits !== 16 && bits !== 8) throw new Error(`bitsDosPesos deve ser 64, 16 ou 8, não ${bits}`);
      this.passoDoPeso = Float64Array.from(this.wMaxDoTipo, (wMax) => wMax / (2 ** bits - 1));
      this.maiorCodigo = 2 ** bits - 1;
      this.arredondar = mulberry32(0x5bd1e995);
      const valores = this.sinapse.w;
      this.sinapse.w = bits === 8 ? new Uint8Array(total) : new Uint16Array(total);
      for (let k = 0; k < total; k++) this.gravarPeso(k, valores[k]);
    }
    const s = this.sinapse;
    const saidas = this.neuronios.map(() => []);
    const entradas = this.neuronios.map(() => []);
    const entradasEE = this.neuronios.map(() => []);
    const idsEE = [];
    for (let k = 0; k < total; k++) {
      saidas[s.pre[k]].push(k);
      entradas[s.pos[k]].push(k);
      if (s.tipo[k] !== SINAPSE_EE) continue;
      entradasEE[s.pos[k]].push(k);
      idsEE.push(k);
    }
    this.saidas = new ListasDeIds(saidas);
    this.entradas = new ListasDeIds(entradas);
    this.entradasEE = new ListasDeIds(entradasEE);
    this.idsEE = Int32Array.from(idsEE);
    this.paresEE = new Set(idsEE.map((k) => s.pre[k] * this.n + s.pos[k]));
  }

  // As saídas procedurais do neurônio i (E→I se i é excitatório, I→I se é inibitório): cada par
  // (i, j) existe com probabilidade pConexao e tem peso lognormal, os dois tirados de um hash da
  // semente da fiação, sem nada guardado. Chama fazer(j, tipo, w) para cada uma.
  saidasProcedurais(i, fazer) {
    const { nExc, pConexao, sementeDaFiacao } = this.config;
    const tipo = i < nExc ? SINAPSE_EI : SINAPSE_II;
    const { mediana, wMax } = this.pesos[TIPOS_DE_SINAPSE[tipo]];
    for (let j = nExc; j < this.n; j++) {
      if (j === i || hashUniforme(sementeDaFiacao, i, j, 0) >= pConexao) continue;
      // Box-Muller com dois números do hash, como em amostraLognormal(mediana, 0.5)
      const u = 1 - hashUniforme(sementeDaFiacao, i, j, 1);
      const normal = Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * hashUniforme(sementeDaFiacao, i, j, 2));
      fazer(j, tipo, Math.min(wMax, mediana * Math.exp(0.5 * normal)));
    }
  }

  // Chama fazer({ pre, pos, tipo, w }) para cada sinapse, guardada ou procedural
  paraCadaSinapse(fazer) {
    for (let k = 0; k < this.nSinapses; k++) fazer(this.vistaDaSinapse(k));
    if (!this.config.conexoesProcedurais) return;
    for (let i = 0; i < this.n; i++) this.saidasProcedurais(i, (pos, tipo, w) => fazer({ pre: i, pos, tipo: TIPOS_DE_SINAPSE[tipo], w }));
  }

  // O peso da sinapse k. Com bitsDosPesos = 16 ou 8, w guarda um código inteiro de 0 a 2^bits − 1,
  // e o peso é o código vezes o passo do tipo (w_max do tipo / (2^bits − 1)).
  peso(k) {
    const s = this.sinapse;
    return this.passoDoPeso === null ? s.w[k] : s.w[k] * this.passoDoPeso[s.tipo[k]];
  }

  // Grava o peso da sinapse k. Quantizado, o valor vai para um dos dois códigos vizinhos com
  // probabilidade proporcional à proximidade (arredondamento estocástico), então mudanças menores
  // que um passo valem em média. O gerador é próprio e não mexe no da simulação.
  gravarPeso(k, valor) {
    const s = this.sinapse;
    if (this.passoDoPeso === null) {
      s.w[k] = valor;
      return;
    }
    const x = valor / this.passoDoPeso[s.tipo[k]];
    const piso = Math.floor(x);
    s.w[k] = Math.min(this.maiorCodigo, Math.max(0, piso + (this.arredondar() < x - piso ? 1 : 0)));
  }

  // Modo exato: com M constante desde a última visita, o traço vira peso pela solução exata de
  // dw/dt = M·e/τ e de/dt = −e/τ: Δw = M·e·(1 − e^(−Δt/τ)) e e ← e·e^(−Δt/τ). Cada sinapse só é
  // visitada quando um spike a toca ou quando alguém precisa dos pesos.
  sincronizarSinapse(k) {
    const s = this.sinapse;
    if (s.elegibilidade[k] !== 0) {
      const decai = Math.exp(-(this.t - s.tElegibilidade[k]) / this.plasticidade.tauElegibilidade);
      this.gravarPeso(k, limiteRigido(this.peso(k) + this.plasticidadeSincronizada * s.elegibilidade[k] * (1 - decai), this.pesos.EE.wMax));
      s.elegibilidade[k] *= decai;
      if (Math.abs(s.elegibilidade[k]) < 1e-12) s.elegibilidade[k] = 0;
    }
    s.tElegibilidade[k] = this.t;
  }

  // O peso que a sinapse E→E k teria se fosse sincronizada agora, sem sincronizá-la. É para as
  // sondas: sincronizar em outros instantes muda o arredondamento, e a simulação deixaria de ser a mesma.
  pesoAtual(k) {
    const s = this.sinapse;
    if (!this.config.elegibilidadeExata || s.elegibilidade[k] === 0) return this.peso(k);
    const decai = Math.exp(-(this.t - s.tElegibilidade[k]) / this.plasticidade.tauElegibilidade);
    return limiteRigido(this.peso(k) + this.plasticidadeSincronizada * s.elegibilidade[k] * (1 - decai), this.pesos.EE.wMax);
  }

  // Deixa todos os pesos E→E em dia (no modo de Euler eles já estão)
  sincronizarPesos() {
    if (!this.config.elegibilidadeExata) return;
    for (const k of this.idsEE) this.sincronizarSinapse(k);
  }

  // Plasticidade estrutural: a cada intervalo, as sinapses E→E mais fracas (uma fração do total,
  // entre as que já têm idadeMinima) são podadas, e o mesmo número nasce entre pares E→E ao acaso
  // ainda sem conexão, com pesoInicial × o peso mediano atual. Sinapses novas fracas só passam da
  // carência (idadeMinima) se a atividade as fortalecer. Empates (pesos iguais) são sorteados. Cada
  // sinapse nova reaproveita a vaga de uma podada, então os índices e o total não mudam.
  religar() {
    const { fracao, idadeMinima, pesoInicial = 1 } = this.config.plasticidadeEstrutural;
    const { nExc } = this.config;
    const s = this.sinapse;
    this.sincronizarPesos();
    const candidatas = [];
    for (const k of this.idsEE) if (this.t - s.nascimento[k] >= idadeMinima) candidatas.push({ k, sorteio: aleatorio() });
    candidatas.sort((a, b) => this.peso(a.k) - this.peso(b.k) || a.sorteio - b.sorteio);
    const podadas = candidatas.slice(0, Math.round(fracao * this.idsEE.length)).map((c) => c.k);
    const pesosOrdenados = Array.from(this.idsEE, (k) => this.peso(k)).sort((a, b) => a - b);
    const mediana = pesosOrdenados[Math.floor(pesosOrdenados.length / 2)];
    for (const k of podadas) {
      this.paresEE.delete(s.pre[k] * this.n + s.pos[k]);
      this.saidas.tirar(s.pre[k], k);
      this.entradas.tirar(s.pos[k], k);
      this.entradasEE.tirar(s.pos[k], k);
      let pre;
      let pos;
      do {
        pre = Math.floor(aleatorio() * nExc);
        pos = Math.floor(aleatorio() * nExc);
      } while (pre === pos || this.paresEE.has(pre * this.n + pos));
      s.pre[k] = pre;
      s.pos[k] = pos;
      this.gravarPeso(k, pesoInicial * mediana);
      s.elegibilidade[k] = 0;
      s.tElegibilidade[k] = this.t;
      s.nascimento[k] = this.t;
      this.paresEE.add(pre * this.n + pos);
      this.saidas.por(pre, k);
      this.entradas.por(pos, k);
      this.entradasEE.por(pos, k);
    }
  }

  // Ruído multiplicativo: em dtMs, ln w de cada sinapse E→E anda σ·√Δt·N(0, 1) − σ²Δt/2 (o
  // último termo mantém a média de w). Não depende de spikes; o teto continua valendo.
  flutuarPesos(dtMs) {
    const { ruidoMultiplicativo: sigma } = this.config;
    const dtS = dtMs / 1000;
    this.sincronizarPesos();
    for (const k of this.idsEE) {
      this.gravarPeso(k, Math.min(this.pesos.EE.wMax, this.peso(k) * Math.exp(sigma * Math.sqrt(dtS) * gaussiana() - (sigma * sigma * dtS) / 2)));
    }
  }

  // Spikes Poisson extras em `alvos` durante `duracao` ms
  estimular(alvos, duracao = 200, taxaHz = 4000) {
    this.estimulos.push({ alvos, ate: this.t + duracao, taxaHz });
  }

  // Eventos do ambiente: soltam dopamina ou noradrenalina fásica
  recompensar() {
    this.moduladores.dopaminaFasica += 1;
  }

  surpreender() {
    this.moduladores.noradrenalinaFasica += 1;
  }

  // Os níveis tônicos andam para os do estado atual; os fásicos decaem. Daí saem os efeitos. Com
  // moduladoresDeFora, os níveis são os que as regiões mandaram (moduladoresRecebidos).
  atualizarModuladores() {
    const m = this.moduladores;
    if (this.config.moduladoresDeFora) {
      Object.assign(m, this.moduladoresRecebidos);
    } else {
      const alvo = estadosCerebrais[this.config.estado];
      m.acetilcolina = alvo.acetilcolina + (m.acetilcolina - alvo.acetilcolina) * this.decaimento.tonico;
      m.noradrenalina = alvo.noradrenalina + (m.noradrenalina - alvo.noradrenalina) * this.decaimento.tonico;
      m.dopaminaFasica *= this.decaimento.fasico;
      m.noradrenalinaFasica *= this.decaimento.fasico;
    }
    calcularEfeitos(m, this.efeitos, this.efeitosDosModuladores);
  }

  // A cada 1 ms: o traço de elegibilidade de cada sinapse E→E vira mudança de peso na proporção
  // do fator M (regra de três fatores do 04 com η = 1/τ_e, para M = 1 dar a STDP direta) e decai
  aplicarElegibilidade(dtMs) {
    const { tauElegibilidade } = this.plasticidade;
    const { wMax } = this.pesos.EE;
    const s = this.sinapse;
    const parametros = { tauE: tauElegibilidade, eta: 1 / tauElegibilidade };
    const uma = { elegibilidade: 0, w: 0 }; // passoTresFatores trabalha sobre um objeto
    for (const k of this.idsEE) {
      if (s.elegibilidade[k] === 0) continue;
      uma.elegibilidade = s.elegibilidade[k];
      uma.w = this.peso(k);
      passoTresFatores(uma, 0, this.efeitos.plasticidade, dtMs, parametros);
      this.gravarPeso(k, limiteRigido(uma.w, wMax));
      s.elegibilidade[k] = Math.abs(uma.elegibilidade) < 1e-9 ? 0 : uma.elegibilidade;
    }
  }

  simular(ms) {
    const passos = Math.round(ms / this.config.dt);
    for (let k = 0; k < passos; k++) this.passo();
  }

  passo() {
    const { dt, entradaFundo, gFundo, escalonamento, gruposCorrelacionados, taxaCorrelacionada, elegibilidadeExata, plasticidadeEstrutural, registrarTraco } = this.config;
    this.t += dt;
    this.atualizarModuladores();
    // No modo exato, se M mudou, todas as sinapses são sincronizadas com o M antigo antes de seguir
    if (elegibilidadeExata && Math.abs(this.efeitos.plasticidade - this.plasticidadeSincronizada) > 1e-12) {
      this.sincronizarPesos();
      this.plasticidadeSincronizada = this.efeitos.plasticidade;
    }
    const gExterno = gFundo * this.efeitos.ganhoExterno;
    this.estimulos = this.estimulos.filter((e) => e.ate > this.t);
    for (const { alvos, taxaHz } of this.estimulos) {
      for (const i of alvos) this.neuronios[i].gAmpa += gExterno * amostraPoisson((taxaHz * dt) / 1000);
    }
    // Cada fonte comum manda os mesmos spikes para todo o seu grupo (entrada correlacionada)
    for (const grupo of gruposCorrelacionados) {
      const spikesDaFonte = amostraPoisson((taxaCorrelacionada * dt) / 1000);
      if (spikesDaFonte > 0) for (const i of grupo) this.neuronios[i].gAmpa += gExterno * spikesDaFonte;
    }
    const { rajadasDeGrupo } = this.config;
    if (rajadasDeGrupo) {
      this.rajadaAte ??= gruposCorrelacionados.map(() => 0);
      gruposCorrelacionados.forEach((grupo, g) => {
        if (this.t < this.rajadaAte[g]) {
          for (const i of grupo) this.neuronios[i].gAmpa += gExterno * amostraPoisson((rajadasDeGrupo.entradaHz * dt) / 1000);
        } else if (aleatorio() < (rajadasDeGrupo.taxaHz * dt) / 1000) {
          this.rajadaAte[g] = this.t + rajadasDeGrupo.duracao;
        }
      });
    }

    const disparos = [];
    const lambdaFundo = (entradaFundo * dt) / 1000;
    for (let i = 0; i < this.n; i++) {
      const n = this.neuronios[i];
      n.gAmpa += gExterno * amostraPoisson(lambdaFundo);
      const corrente = -n.gAmpa * n.v - n.gNmda * bloqueioMg(n.v) * n.v + n.gGaba * (this.eGaba - n.v);
      const disparou = n.adex
        ? passoAdExClopath(n, parametrosAdExClopath, this.config.ganhoAdEx * corrente, dt)
        : passoIzhikevich(n, n.izh, corrente, dt);
      if (disparou) {
        // o passo somou o salto da adaptação (d ou b); a noradrenalina o escala
        if (n.adex) n.w += parametrosAdExClopath.b * (this.efeitos.adaptacao - 1);
        else n.u += n.izh.d * (this.efeitos.adaptacao - 1);
        disparos.push(i);
      }
      if (i === this.selecionado && registrarTraco) this.registro.traco.push(disparou ? 30 : n.v);
      n.gAmpa *= this.decaimento.ampa;
      n.gNmda *= this.decaimento.nmda;
      n.gGaba *= this.decaimento.gaba;
      n.traco *= this.decaimento.traco;
      n.r1 *= this.decaimento.r1;
      n.o1 *= this.decaimento.o1;
      n.o2 *= this.decaimento.o2;
      n.taxa *= this.decaimento.taxa;
    }

    // Primeiro a plasticidade, com os traços de antes dos spikes deste passo; depois os traços
    if (this.clopath) this.passoClopath();
    for (const i of disparos) this.disparar(i);
    for (const i of disparos) {
      const n = this.neuronios[i];
      n.traco += 1;
      n.r1 += 1;
      n.o1 += 1;
      n.o2 += 1;
      n.taxa += 1000 / this.plasticidade.tauTaxa;
      if (this.clopath && i < this.config.nExc) this.clopath.xBarra[i] += 1 / this.plasticidade.clopath.tauX;
      this.registro.spikes.push(i, Math.round(this.t * 100) / 100);
    }
    const passoAtual = Math.round(this.t / dt);
    if (!elegibilidadeExata && passoAtual % Math.round(1 / dt) === 0) this.aplicarElegibilidade(1);
    if (escalonamento && passoAtual % Math.round(100 / dt) === 0) this.escalonar();
    if (this.config.ruidoMultiplicativo > 0 && passoAtual % Math.round(100 / dt) === 0) this.flutuarPesos(100);
    if (plasticidadeEstrutural && passoAtual % Math.round(plasticidadeEstrutural.intervalo / dt) === 0) this.religar();
  }

  // Um spike de i: entrega a condutância nas saídas e aplica a plasticidade nas saídas (i é o pré)
  // e nas entradas (i é o pós)
  disparar(i) {
    const { stp, stdp, istdp, razaoNMDA, regraSTDP, elegibilidadeExata, recorrenciaEE } = this.config;
    const p = this.plasticidade;
    const { a2Menos, a2Mais, a3Mais } = p.tripletos;
    const alfa = alfaVogels(p.taxaAlvo, p.tauTraco);
    const disparou = this.neuronios[i];
    // Amplitude da LTP neste spike pós: tripletos (depende do traço lento o2) ou pares (constante).
    // Na regra de Clopath a LTP é contínua (passoClopath), e aqui fica só a LTD do spike pré.
    const amplitudeLTP = regraSTDP === "pares" ? p.aParesMais : a2Mais + a3Mais * disparou.o2;
    const clopath = regraSTDP === "clopath";
    // depressão de curto prazo: a mesma liberação em todas as saídas de um excitatório
    const liberacao = stp && i < this.config.nExc ? liberarTM(disparou.tm, p.tm, this.t) / p.tm.U : 1;
    const s = this.sinapse;
    const saidas = this.saidas;
    for (let q = saidas.inicio[i], fim = q + saidas.quantas[i]; q < fim; q++) {
      const k = saidas.ids[q];
      const tipo = s.tipo[k];
      const alvo = this.neuronios[s.pos[k]];
      const wMax = this.wMaxDoTipo[tipo];
      if (elegibilidadeExata && tipo === SINAPSE_EE) this.sincronizarSinapse(k);
      if (tipo === SINAPSE_EE || tipo === SINAPSE_EI) {
        if (recorrenciaEE || tipo !== SINAPSE_EE) {
          const eficacia = this.peso(k) * liberacao * (tipo === SINAPSE_EE ? this.efeitos.recorrencia : 1);
          alvo.gAmpa += eficacia;
          alvo.gNmda += razaoNMDA * eficacia;
        }
        if (stdp && tipo === SINAPSE_EE && clopath) {
          // LTD de Clopath: −A_LTD·(ū̄²/u_ref²)·[ū₋ − θ₋]₊, com o ū₋ atrasado do pós
          const c = this.clopath;
          const parametros = p.clopath;
          const excesso = c.uMenosAtrasado[s.pos[k]] - parametros.thetaMenos;
          if (excesso > 0) {
            s.elegibilidade[k] -= (this.pesos.EE.escalaLTP ?? wMax) * parametros.aLTD * ((c.media[s.pos[k]] ** 2) / parametros.uRef2) * excesso;
          }
        } else if (stdp && tipo === SINAPSE_EE) s.elegibilidade[k] += ltdSuave(this.peso(k), a2Menos * alvo.o1);
      } else {
        alvo.gGaba += this.peso(k);
        if (istdp && tipo === SINAPSE_IE) this.gravarPeso(k, Math.min(wMax, istdpPre(this.peso(k), alvo.traco, alfa, p.etaInib)));
      }
    }
    if (this.config.conexoesProcedurais) {
      this.saidasProcedurais(i, (j, tipo, w) => {
        const alvo = this.neuronios[j];
        if (tipo === SINAPSE_EI) {
          alvo.gAmpa += w * liberacao;
          alvo.gNmda += razaoNMDA * w * liberacao;
        } else alvo.gGaba += w;
      });
    }
    const entradas = this.entradas;
    for (let q = entradas.inicio[i], fim = q + entradas.quantas[i]; q < fim; q++) {
      const k = entradas.ids[q];
      const tipo = s.tipo[k];
      const origem = this.neuronios[s.pre[k]];
      const wMax = this.wMaxDoTipo[tipo];
      if (elegibilidadeExata && tipo === SINAPSE_EE) this.sincronizarSinapse(k);
      if (stdp && tipo === SINAPSE_EE && !clopath) s.elegibilidade[k] += (this.pesos.EE.escalaLTP ?? wMax) * origem.r1 * amplitudeLTP;
      if (istdp && tipo === SINAPSE_IE) this.gravarPeso(k, Math.min(wMax, istdpPos(this.peso(k), origem.traco, p.etaInib)));
    }
  }

  // Escalonamento sináptico das entradas E→E de cada neurônio excitatório
  escalonar() {
    const { wMax } = this.pesos.EE;
    this.sincronizarPesos();
    for (let j = 0; j < this.config.nExc; j++) {
      const indices = this.entradasEE.lista(j);
      const pesos = Array.from(indices, (k) => this.peso(k));
      escalonamentoSinaptico(pesos, this.neuronios[j].taxa, this.plasticidade.taxaAlvo, this.plasticidade.epsilon);
      indices.forEach((k, m) => this.gravarPeso(k, Math.min(wMax, pesos[m])));
    }
  }

  // Devolve e limpa o que aconteceu desde a última chamada (para a visualização)
  esvaziarRegistro() {
    const registro = this.registro;
    this.registro = { spikes: [], traco: [] };
    return registro;
  }

  estrutura() {
    return {
      nExc: this.config.nExc,
      nInib: this.config.nInib,
      dt: this.config.dt,
      grupo: this.grupo,
      sinapses: this.listaDeSinapses().flatMap(({ pre, pos }) => [pre, pos]),
      wMax: Object.fromEntries(Object.entries(this.pesos).map(([tipo, { wMax }]) => [tipo, wMax])),
      config: this.config,
    };
  }

  // A sinapse k como objeto { pre, pos, tipo ("EE", "EI", "IE" ou "II"), w }, para filtros e leituras
  vistaDaSinapse(k) {
    const s = this.sinapse;
    return { pre: s.pre[k], pos: s.pos[k], tipo: TIPOS_DE_SINAPSE[s.tipo[k]], w: this.peso(k) };
  }

  // Todas as sinapses como { pre, pos, tipo, w }, na ordem de paraCadaSinapse
  listaDeSinapses() {
    const lista = [];
    this.paraCadaSinapse((sinapse) => lista.push(sinapse));
    return lista;
  }

  // Peso médio das sinapses que passam no filtro, que recebe { pre, pos, tipo, w }
  pesoMedio(filtro) {
    const pesos = [];
    this.paraCadaSinapse((sinapse) => {
      if (filtro(sinapse)) pesos.push(sinapse.w);
    });
    return media(pesos);
  }
}

// Roda o cérebro sem visualização e mostra o que acontece. Rode com: node index.js --cerebro
//   1–10 s   acordado, espontâneo
//   11–20 s  o grupo do botão é estimulado 1×/s
//   21–30 s  acordado
//   31–40 s  sono NREM (ACh e NA baixas)
//   41–45 s  acordado de novo
// Depois compara cérebros novos estimulados com e sem dopamina logo após o estímulo.
function demonstracaoCerebro() {
  const cerebro = new Cerebro();
  const noGrupo = new Set(cerebro.grupo);
  const dentroDoGrupo = (s) => s.tipo === "EE" && noGrupo.has(s.pre) && noGrupo.has(s.pos);
  const foraDoGrupo = (s) => s.tipo === "EE" && !dentroDoGrupo(s);
  const taxas = (spikes) => {
    const contagem = { grupo: 0, resto: 0, inib: 0 };
    for (let k = 0; k < spikes.length; k += 2) {
      const i = spikes[k];
      contagem[noGrupo.has(i) ? "grupo" : cerebro.ehExcitatorio(i) ? "resto" : "inib"]++;
    }
    const nResto = cerebro.config.nExc - noGrupo.size;
    return `grupo ${hz(contagem.grupo / noGrupo.size)} · resto ${hz(contagem.resto / nResto)} · I ${hz(contagem.inib / cerebro.config.nInib)}`;
  };
  console.log(`\nCérebro: ${cerebro.n} neurônios, ${cerebro.nSinapses} sinapses`);
  for (let s = 1; s <= 45; s++) {
    cerebro.config.estado = s > 30 && s <= 40 ? "nrem" : "vigilia";
    if (s > 10 && s <= 20) cerebro.estimular(cerebro.grupo, 200);
    cerebro.simular(1000);
    const { spikes } = cerebro.esvaziarRegistro();
    const fase = s <= 10 ? "acordado" : s <= 20 ? "estimula o grupo" : s <= 30 ? "acordado" : s <= 40 ? "NREM" : "acordado";
    const { acetilcolina, noradrenalina } = cerebro.moduladores;
    linha(
      `t = ${s} s (${fase})`,
      `${taxas(spikes)} · w no grupo ${cerebro.pesoMedio(dentroDoGrupo).toFixed(4)} · fora ${cerebro.pesoMedio(foraDoGrupo).toFixed(4)} · ACh ${acetilcolina.toFixed(2)} · NA ${noradrenalina.toFixed(2)}`,
    );
  }

  console.log("\nDopamina como terceiro fator: 3 estímulos do grupo em 6 cérebros novos, recompensa 300 ms depois de cada um");
  for (const comRecompensa of [false, true]) {
    const mudancas = [];
    for (let k = 0; k < 6; k++) {
      const novo = new Cerebro();
      const grupo = new Set(novo.grupo);
      const dentro = (s) => s.tipo === "EE" && grupo.has(s.pre) && grupo.has(s.pos);
      novo.simular(3000);
      const antes = novo.pesoMedio(dentro);
      for (let estimulo = 0; estimulo < 3; estimulo++) {
        novo.estimular(novo.grupo, 200);
        novo.simular(500);
        if (comRecompensa) novo.recompensar();
        novo.simular(500);
      }
      mudancas.push(novo.pesoMedio(dentro) - antes);
    }
    linha(comRecompensa ? "com recompensa" : "sem recompensa", `Δw médio no grupo ${media(mudancas).toFixed(4)} (${mudancas.map((d) => d.toFixed(3)).join(" ")})`);
  }
}

// ============================================================================
// Volume de informação: memória, sondas em disco e fila de processos paralelos
// ============================================================================

// Memória do processo em MB: rss (tudo o que o processo ocupa), heap (objetos JS), arrays (arrays
// tipados) e a memória livre do sistema
function memoriaEmMB() {
  const { rss, heapUsed, arrayBuffers } = process.memoryUsage();
  const mb = (bytes) => Math.round(bytes / 2 ** 20);
  return { rss: mb(rss), heap: mb(heapUsed), arrays: mb(arrayBuffers), livre: mb(freemem()) };
}

// Sondas: variáveis lidas com taxa reduzida e gravadas num CSV em blocos de linhas, para uma
// simulação longa não guardar tudo na RAM. variaveis = { nome: () => valor }; um valor que não
// existe naquela linha (null ou undefined) fica vazio.
class Sondas {
  constructor(arquivo, variaveis, { linhasPorBloco = 100 } = {}) {
    this.arquivo = arquivo;
    this.variaveis = Object.entries(variaveis);
    this.linhasPorBloco = linhasPorBloco;
    this.linhas = [];
    mkdirSync(dirname(arquivo), { recursive: true });
    writeFileSync(arquivo, `${this.variaveis.map(([nome]) => nome).join(",")}\n`);
  }

  amostrar() {
    const valor = (x) => (x == null || !Number.isFinite(x) ? "" : Number(x.toPrecision(6)));
    this.linhas.push(this.variaveis.map(([, ler]) => valor(ler())).join(","));
    if (this.linhas.length >= this.linhasPorBloco) this.descarregar();
  }

  descarregar() {
    if (this.linhas.length === 0) return;
    appendFileSync(this.arquivo, `${this.linhas.join("\n")}\n`);
    this.linhas = [];
  }
}

// Fila de tarefas em processos paralelos, de olho na memória. Cada linha do arquivo são os
// argumentos de um `node index.js --conectoma ...`. Uma tarefa nova só começa se há menos de
// `paralelos` rodando e mais de memoriaMinima MB livres no sistema; o log de cada uma vai para
// <logs>/<argumentos>.txt. Rode com:
//   node index.js --fila=<arquivo> [--paralelos=4] [--memoriaMinima=1000] [--logs=resultados/logs]
function rodarFila() {
  const tarefas = readFileSync(lerArgumento("fila"), "utf8").split(/\r?\n/).map((l) => l.trim()).filter(Boolean);
  const paralelos = Number(lerArgumento("paralelos", 4));
  const memoriaMinima = Number(lerArgumento("memoriaMinima", 1000));
  const logs = lerArgumento("logs", join("resultados", "logs"));
  mkdirSync(logs, { recursive: true });
  const script = fileURLToPath(import.meta.url);
  const hora = () => new Date().toTimeString().slice(0, 8);
  let proxima = 0;
  let rodando = 0;
  let falhas = 0;
  let menorLivre = Infinity;
  let esperando = false;
  console.log(`${hora()} fila: ${tarefas.length} tarefas, até ${paralelos} em paralelo, só começa uma com mais de ${memoriaMinima} MB livres`);
  const relogio = setInterval(() => {
    const { livre } = memoriaEmMB();
    menorLivre = Math.min(menorLivre, livre);
    while (rodando < paralelos && proxima < tarefas.length && livre > memoriaMinima) {
      const argumentos = tarefas[proxima++];
      const nome = argumentos.replace(/--/g, "").replace(/[^\w.,=-]+/g, "_");
      const saida = openSync(join(logs, `${nome}.txt`), "w");
      const inicio = performance.now();
      const filho = spawn(process.execPath, [script, "--conectoma", ...argumentos.split(/\s+/)], { stdio: ["ignore", saida, saida] });
      rodando++;
      console.log(`${hora()} começa ${nome} (${livre} MB livres)`);
      filho.on("exit", (codigo) => {
        closeSync(saida);
        rodando--;
        if (codigo !== 0) falhas++;
        console.log(`${hora()} fim ${nome}: código ${codigo}, ${Math.round((performance.now() - inicio) / 1000)} s`);
        if (proxima === tarefas.length && rodando === 0) {
          clearInterval(relogio);
          console.log(`${hora()} fila concluída: ${tarefas.length - falhas} ok, ${falhas} com erro; menor memória livre vista: ${menorLivre} MB`);
        }
      });
      break; // uma por vez: a memória livre é medida de novo antes da próxima
    }
    const semMemoria = livre <= memoriaMinima && rodando < paralelos && proxima < tarefas.length;
    if (semMemoria && !esperando) console.log(`${hora()} esperando memória: ${livre} MB livres`);
    esperando = semMemoria;
  }, 2000);
}

// ============================================================================
// Experimento --conectoma: as regras de plasticidade do cérebro produzem, sozinhas, as
// estatísticas de conectividade de conectomas reais?
//   rede: 500 neurônios (80% E), conectividade 0,1, pesos E→E iniciais todos iguais
//   entrada: 8 grupos de excitatórios; além do fundo independente, cada grupo recebe os spikes de
//            uma fonte comum (20% da entrada) ou entra em rajadas de taxa alta
//   Fase 1 e teste extra: a fiação é fixa e só os pesos mudam. Fase 2: poda e criação de sinapses.
//   Testes de regra (--fase=regras): variantes da homeostase e a regra de Clopath.
// Cada semente vira um registro em disco (fiação e pesos E→E no início e no fim, a configuração e
// os spikes das janelas de medida), e --analisar=<pasta> refaz todas as medidas a partir deles.
// ============================================================================

const experimentoConectoma = {
  nNeuronios: 500,
  pConexao: 0.1,
  nGrupos: 8,
  fracaoCorrelacionada: 0.2,
  entradaTotal: configuracaoCerebro.entradaFundo, // Hz de entrada externa por neurônio
  taxaAlvo: plasticidadeCerebro.taxaAlvo, // Hz do escalonamento e do iSTDP
  estrutural: null, // a Fase 2 liga a plasticidade estrutural
  rajadas: null, // o teste extra liga rajadas por grupo (ver rajadasDeGrupo)
  fatorTeto: 1, // o teste da lognormal sobe o teto E→E sem mudar a escala da LTP
  ruidoMultiplicativo: 0, // por √s (ver flutuarPesos)
  elegibilidadeExata: true,
  segundos: 900, // a 600 s o CV e a correlação recíproca ainda derivam um pouco
  janelaDeMedida: 20000, // ms de spikes para medir a semelhança das respostas
  larguraDoBin: 50, // ms
  transiente: 2000, // ms descartados antes de cada janela com os pesos congelados
  memoriaMinimaMB: 800, // abaixo disso de memória livre no sistema, a simulação avisa
  bitsDosPesos: 64, // 16 ou 8 guarda os pesos como inteiros (ver gravarPeso)
  conexoesProcedurais: false, // true: E→I e I→I saem de um hash da semente (ver saidasProcedurais)
  sementes: [1, 2, 3, 4, 5],
  condicoes: ["tripletos", "pares", "sem plasticidade"],
};

// Excitatórios AdEx de Clopath. Com ganho 281 (o mesmo dV/dt do Izhikevich) a rede começa com os
// excitatórios a 3,3 Hz (o limiar adaptativo e a adaptação seguram); com 950 ela começa a 8,9 Hz,
// como a de Izhikevich (9,0 Hz; rajadas, sem plasticidade, primeiros 20 s).
const adexDoConectoma = { modeloExcitatorio: "adex", ganhoAdEx: 950 };

// A regra de Clopath calibrada para esta rede (somas com os pesos parados, rajadas, 20 s):
//   u_ref²: com os 60 mV² do artigo (u_ref ≈ 7,7 mV) a LTD sai 2,9× maior que a LTP, porque aqui
//   os neurônios ficam bem despolarizados (ū̄ ≈ 23 mV); com 176 mV² as duas se igualam no começo
//   A_LTP e A_LTD × 0,05: com as amplitudes do artigo a LTP bruta é 7,8·10⁻² w_max por sinapse
//   por segundo, 20× a dos tripletos nos mesmos neurônios (4,0·10⁻³); assim as duas regras mudam
//   os pesos na mesma velocidade e diferem só na forma
const clopathDoConectoma = {
  ...plasticidadeCerebro.clopath,
  uRef2: 176,
  aLTP: 0.05 * parametrosClopath.aLTP,
  aLTD: 0.05 * parametrosClopath.aLTD,
};

// O que cada condição muda no cérebro. congelarHomeostaseEm (s) é do experimento: nesse instante o
// escalonamento e o iSTDP param, e os pesos I→E e a escala dos E→E ficam onde estão.
const condicoesDoConectoma = {
  tripletos: {},
  pares: { regraSTDP: "pares" },
  "sem plasticidade": { stdp: false, escalonamento: false, istdp: false },
  "homeostase congelada": { congelarHomeostaseEm: 300 },
  "sem escalonamento": { escalonamento: false },
  "sem istdp": { istdp: false },
  "tripletos adex": adexDoConectoma,
  "clopath adex": { ...adexDoConectoma, regraSTDP: "clopath", plasticidade: { clopath: clopathDoConectoma } },
};

// Pesos de uma rede maior: cada tipo de conexão é dividido pelo aumento no número médio de
// entradas daquele tipo, para a corrente total por neurônio ficar como na rede calibrada
// (100 E e 25 I com conectividade 0,2). O iSTDP é absoluto e escala junto com os pesos I→E.
function escalaDaRede(nExc, nInib, pConexao) {
  const fator = { E: (100 * 0.2) / (nExc * pConexao), I: (25 * 0.2) / (nInib * pConexao) };
  const pesos = Object.fromEntries(
    Object.entries(pesosPorTipo).map(([tipo, { mediana, wMax }]) => [tipo, { mediana: mediana * fator[tipo[0]], wMax: wMax * fator[tipo[0]] }]),
  );
  return { pesos, plasticidade: { etaInib: plasticidadeCerebro.etaInib * fator.I } };
}

function criarCerebroDoConectoma(condicao, e) {
  if (!(condicao in condicoesDoConectoma)) throw new Error(`condição desconhecida: ${condicao}`);
  const { nNeuronios, pConexao, nGrupos, fracaoCorrelacionada, entradaTotal, taxaAlvo } = e;
  const nExc = Math.round(0.8 * nNeuronios);
  const nInib = nNeuronios - nExc;
  const tamanho = nExc / nGrupos;
  const grupos = Array.from({ length: nGrupos }, (_, g) => Array.from({ length: tamanho }, (_, i) => g * tamanho + i));
  const escala = escalaDaRede(nExc, nInib, pConexao);
  // a regra em pares tem o mesmo equilíbrio dos tripletos na taxa-alvo (ver aParesMais)
  const aParesMais = parametrosTripletos.a3Mais * (taxaAlvo / 1000) * parametrosTripletos.tauY;
  const { wMax } = escala.pesos.EE;
  const { congelarHomeostaseEm, plasticidade = {}, ...mudancas } = condicoesDoConectoma[condicao];
  return new Cerebro({
    nExc,
    nInib,
    pConexao,
    pesos: { ...escala.pesos, EE: { ...escala.pesos.EE, wMax: wMax * e.fatorTeto, escalaLTP: wMax } },
    ruidoMultiplicativo: e.ruidoMultiplicativo,
    plasticidade: { ...escala.plasticidade, taxaAlvo, aParesMais, ...plasticidade },
    pesosIniciaisIguais: true,
    gruposCorrelacionados: grupos,
    taxaCorrelacionada: fracaoCorrelacionada * entradaTotal,
    entradaFundo: (1 - fracaoCorrelacionada) * entradaTotal,
    elegibilidadeExata: e.elegibilidadeExata,
    plasticidadeEstrutural: e.estrutural,
    rajadasDeGrupo: e.rajadas,
    registrarTraco: false,
    bitsDosPesos: e.bitsDosPesos,
    conexoesProcedurais: e.conexoesProcedurais,
    sementeDaFiacao: e.semente ?? 1,
    ...mudancas,
  });
}

// --- Registros: o que vai para o disco -------------------------------------------------

// O que as medidas precisam saber da rede
function redeDoCerebro(cerebro) {
  const { nExc, nInib, dt, gruposCorrelacionados } = cerebro.config;
  const { wMax: teto, escalaLTP = teto } = cerebro.pesos.EE;
  return { nExc, nInib, dt, grupos: gruposCorrelacionados, escala: escalaLTP, teto };
}

// Retrato da fiação E→E: a sinapse k vai de pre[k] para pos[k] com peso w[k]
function retratar(cerebro) {
  cerebro.sincronizarPesos();
  const { pre, pos } = cerebro.sinapse;
  const ids = cerebro.idsEE;
  return { pre: Array.from(ids, (k) => pre[k]), pos: Array.from(ids, (k) => pos[k]), w: Array.from(ids, (k) => cerebro.peso(k)) };
}

// Congela o cérebro (pesos E→E em dia e sem STDP, homeostase, poda nem ruído) e grava duas janelas:
// com a recorrência E→E e sem ela (só entrada externa e inibição). O gerador é semeado de novo
// antes de cada uma, então as duas recebem exatamente a mesma entrada externa.
function janelasCongeladas(cerebro, semente, e) {
  cerebro.sincronizarPesos();
  for (const k of cerebro.idsEE) cerebro.sinapse.elegibilidade[k] = 0;
  Object.assign(cerebro.config, { stdp: false, escalonamento: false, istdp: false, plasticidadeEstrutural: null, ruidoMultiplicativo: 0 });
  const janelas = {};
  for (const [nome, recorrenciaEE] of [["comRecorrencia", true], ["semRecorrencia", false]]) {
    cerebro.config.recorrenciaEE = recorrenciaEE;
    semear(semente + 104729);
    cerebro.rajadaAte = null;
    cerebro.simular(e.transiente);
    cerebro.esvaziarRegistro();
    const de = cerebro.t;
    cerebro.simular(e.janelaDeMedida);
    janelas[nome] = { de, ate: cerebro.t, spikes: cerebro.esvaziarRegistro().spikes };
  }
  cerebro.config.recorrenciaEE = true;
  return janelas;
}

// Sondas do conectoma, uma linha por segundo simulado: as taxas (E, I e de cada grupo) no último
// segundo e, a cada 10 s, o peso E→E médio dentro e fora dos grupos e a memória. Os pesos são
// lidos sem sincronizar as sinapses, então as sondas não mudam a simulação.
function sondasDoConectoma(arquivo, cerebro, rede) {
  const grupoDe = grupoDosNeuronios(rede);
  const agora = { segundo: 0, spikes: [] };
  const contar = (filtro) => {
    let n = 0;
    for (let k = 0; k < agora.spikes.length; k += 2) if (filtro(agora.spikes[k])) n++;
    return n;
  };
  const aCada10s = (ler) => () => (agora.segundo % 10 === 0 ? ler() : null);
  const pesoMedio = (dentro) => () => {
    let soma = 0;
    let n = 0;
    const { pre, pos } = cerebro.sinapse;
    for (const k of cerebro.idsEE) {
      if ((grupoDe[pre[k]] === grupoDe[pos[k]]) !== dentro) continue;
      soma += cerebro.pesoAtual(k);
      n++;
    }
    return soma / n / rede.escala;
  };
  const sondas = new Sondas(arquivo, {
    segundo: () => agora.segundo,
    taxaE: () => contar((i) => i < rede.nExc) / rede.nExc,
    taxaI: () => contar((i) => i >= rede.nExc) / rede.nInib,
    ...Object.fromEntries(rede.grupos.map((g, k) => [`taxaGrupo${k}`, () => contar((i) => i < rede.nExc && grupoDe[i] === k) / g.length])),
    pesoNoGrupo: aCada10s(pesoMedio(true)),
    pesoForaDoGrupo: aCada10s(pesoMedio(false)),
    rssMB: aCada10s(() => memoriaEmMB().rss),
    livreMB: aCada10s(() => memoriaEmMB().livre),
  });
  return {
    amostrar(segundo, spikes) {
      agora.segundo = segundo;
      agora.spikes = spikes;
      sondas.amostrar();
    },
    fechar: () => sondas.descarregar(),
  };
}

// Uma simulação de uma condição, que vira um registro:
//   inicio: fiação e pesos em t = 0 e os spikes dos primeiros 20 s
//   fim: fiação e pesos no fim e os spikes dos últimos 20 s
//   congelado: as duas janelas de janelasCongeladas, com os pesos do fim
//   memoria: o maior rss do processo, medido a cada 10 s
// Com `arquivoDeSondas`, grava as sondas do conectoma nesse CSV. Com `aCada`, chama também
// aoMedir(segundo, medida, cerebro) a cada `aCada` segundos.
function rodarConectoma(condicao, semente, opcoes = {}, aoMedir = null) {
  const e = { ...experimentoConectoma, ...opcoes, semente };
  const relogio = performance.now();
  semear(semente);
  const cerebro = criarCerebroDoConectoma(condicao, e);
  const rede = redeDoCerebro(cerebro);
  const sondas = e.arquivoDeSondas ? sondasDoConectoma(e.arquivoDeSondas, cerebro, rede) : null;
  const congelarEm = condicoesDoConectoma[condicao].congelarHomeostaseEm;
  const inicio = retratar(cerebro);
  let recentes = [];
  let picoRss = 0;
  let avisouMemoria = false;
  const janelaAtual = () => ({ de: cerebro.t - e.janelaDeMedida, ate: cerebro.t, spikes: recentes });
  for (let segundo = 1; segundo <= e.segundos; segundo++) {
    cerebro.simular(1000);
    const { spikes } = cerebro.esvaziarRegistro();
    sondas?.amostrar(segundo, spikes);
    for (const valor of spikes) recentes.push(valor);
    let corte = 0;
    while (corte < recentes.length && recentes[corte + 1] < cerebro.t - e.janelaDeMedida) corte += 2;
    if (corte > 0) recentes = recentes.slice(corte);
    if (segundo * 1000 === e.janelaDeMedida) inicio.janela = { ...janelaAtual(), spikes: recentes.slice() };
    if (segundo === congelarEm) Object.assign(cerebro.config, { escalonamento: false, istdp: false });
    if (aoMedir && e.aCada && segundo % e.aCada === 0) aoMedir(segundo, medirJanela(rede, retratar(cerebro), janelaAtual(), e.larguraDoBin), cerebro);
    if (segundo % 10 === 0) {
      const memoria = memoriaEmMB();
      picoRss = Math.max(picoRss, memoria.rss);
      if (memoria.livre < e.memoriaMinimaMB && !avisouMemoria) {
        console.warn(`  aviso: ${condicao}, semente ${semente}, t = ${segundo} s: só ${memoria.livre} MB livres no sistema`);
        avisouMemoria = true;
      }
    }
  }
  sondas?.fechar();
  const fim = { ...retratar(cerebro), janela: janelaAtual() };
  const congelado = janelasCongeladas(cerebro, semente, e);
  const segundosDeRelogio = Math.round((performance.now() - relogio) / 1000);
  const memoria = { picoRssMB: picoRss };
  return { registro: { versao: 1, condicao, semente, experimento: e, rede, inicio, fim, congelado, segundosDeRelogio, memoria }, cerebro };
}

// O nome dos arquivos de uma semente, sem extensão
const nomeDaSemente = (condicao, semente) => `${condicao.replaceAll(" ", "-")}-semente-${semente}`;

function salvarRegistro(registro, pasta) {
  mkdirSync(pasta, { recursive: true });
  const arquivo = join(pasta, `${nomeDaSemente(registro.condicao, registro.semente)}.json.gz`);
  writeFileSync(arquivo, gzipSync(JSON.stringify(registro)));
  return arquivo;
}

function lerRegistros(pasta) {
  return readdirSync(pasta)
    .filter((nome) => nome.endsWith(".json.gz"))
    .map((nome) => JSON.parse(gunzipSync(readFileSync(join(pasta, nome))).toString("utf8")));
}

// --- Estatística ---------------------------------------------------------------

// Φ(z) pela aproximação de Abramowitz & Stegun (7.1.26) da função erro
function normalAcumulada(z) {
  const x = Math.abs(z) / Math.SQRT2;
  const t = 1 / (1 + 0.3275911 * x);
  const erf = 1 - ((((1.061405429 * t - 1.453152027) * t + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-x * x);
  return z >= 0 ? 0.5 * (1 + erf) : 0.5 * (1 - erf);
}

// Correlação de Pearson; NaN se um dos lados não varia. "Não varia" tem uma tolerância relativa:
// a média de valores idênticos pode diferir deles no último bit, e isso daria r = ±1 espúrio.
function pearson(x, y) {
  const mx = media(x);
  const my = media(y);
  let sxy = 0;
  let sxx = 0;
  let syy = 0;
  for (let i = 0; i < x.length; i++) {
    sxy += (x[i] - mx) * (y[i] - my);
    sxx += (x[i] - mx) ** 2;
    syy += (y[i] - my) ** 2;
  }
  const constante = (s, m) => Math.sqrt(s / x.length) <= 1e-9 * Math.abs(m);
  return constante(sxx, mx) || constante(syy, my) ? NaN : sxy / Math.sqrt(sxx * syy);
}

// Correlação parcial de x e y descontando z
function correlacaoParcial(x, y, z) {
  const rxy = pearson(x, y);
  const rxz = pearson(x, z);
  const ryz = pearson(y, z);
  return (rxy - rxz * ryz) / Math.sqrt((1 - rxz ** 2) * (1 - ryz ** 2));
}

// Se os pesos forem lognormais, ln w é normal: assimetria e curtose em excesso ≈ 0, e a distância
// de Kolmogorov-Smirnov entre ln w e a normal ajustada fica no nível do ruído amostral (o D
// crítico de Lilliefors a 5% é ≈ 0,886/√n). Pesos em zero ficam de fora do ln e são contados.
// `escala` é o w_max da LTP (a referência dos pesos relativos) e `teto` o limite superior.
function estatisticasDePesos(pesos, escala, teto = escala) {
  const n = pesos.length;
  const resultado = {
    mediaRelativa: media(pesos) / escala,
    cv: desvioPadrao(pesos) / media(pesos),
    noTeto: pesos.filter((w) => w >= 0.99 * teto).length / n,
    emZero: pesos.filter((w) => w <= 1e-3 * escala).length / n,
  };
  const logs = pesos.filter((w) => w > 1e-3 * escala).map(Math.log);
  const mu = media(logs);
  const sigma = desvioPadrao(logs);
  if (!(sigma > 1e-9)) return { ...resultado, sigmaLn: 0, assimetria: NaN, curtose: NaN, ks: NaN, ksCritico: NaN };
  const z = logs.map((x) => (x - mu) / sigma).sort((a, b) => a - b);
  let m3 = 0;
  let m4 = 0;
  let ks = 0;
  z.forEach((v, i) => {
    m3 += v ** 3;
    m4 += v ** 4;
    const F = normalAcumulada(v);
    ks = Math.max(ks, Math.abs(F - i / z.length), Math.abs(F - (i + 1) / z.length));
  });
  return { ...resultado, sigmaLn: sigma, assimetria: m3 / z.length, curtose: m4 / z.length - 3, ks, ksCritico: 0.886 / Math.sqrt(z.length) };
}

// --- Medidas dos pesos e das respostas -------------------------------------------------

// grupoDe[i]: o grupo de entrada do excitatório i (−1 se nenhum)
function grupoDosNeuronios(rede) {
  const grupoDe = new Int32Array(rede.nExc).fill(-1);
  rede.grupos.forEach((grupo, g) => grupo.forEach((i) => (grupoDe[i] = g)));
  return grupoDe;
}

// Pares recíprocos (A→B e B→A existem) contra unidirecionais, em todos os pares, só nos do mesmo
// grupo de entrada e só nos de grupos diferentes. A correlação "sem teto" deixa de fora os pares
// em que algum dos dois pesos está no teto. A "por bloco" desconta de cada peso a média do seu
// bloco (grupo do pré → grupo do pós): se cada par de grupos tem o seu nível de peso, e esse nível
// é simétrico, só isso já dá correlação recíproca positiva (o paradoxo de Simpson nos blocos).
function reciprocidade(retrato, grupoDe, teto) {
  const { pre, pos, w } = retrato;
  const n = grupoDe.length;
  const nBlocos = Math.max(...grupoDe) + 2; // o grupo −1 (sem grupo) vira o bloco 0
  const bloco = (a, b) => (grupoDe[a] + 1) * nBlocos + grupoDe[b] + 1;
  const somaDoBloco = new Float64Array(nBlocos * nBlocos);
  const sinapsesDoBloco = new Float64Array(nBlocos * nBlocos);
  pre.forEach((a, k) => {
    somaDoBloco[bloco(a, pos[k])] += w[k];
    sinapsesDoBloco[bloco(a, pos[k])]++;
  });
  const residuo = (k) => w[k] - somaDoBloco[bloco(pre[k], pos[k])] / sinapsesDoBloco[bloco(pre[k], pos[k])];
  // "forte": no quartil de cima do seu bloco (com empates no teto, todas as do teto contam)
  const pesosDoBloco = Array.from({ length: nBlocos * nBlocos }, () => []);
  pre.forEach((a, k) => pesosDoBloco[bloco(a, pos[k])].push(w[k]));
  const quartilDeCima = pesosDoBloco.map((lista) => lista.sort((x, y) => x - y)[Math.floor(0.75 * (lista.length - 1))]);
  const forte = (k) => w[k] >= quartilDeCima[bloco(pre[k], pos[k])];
  const indice = new Map();
  pre.forEach((a, k) => indice.set(a * n + pos[k], k));
  const novo = () => ({ ida: [], volta: [], idaResidual: [], voltaResidual: [], forteIda: [], forteVolta: [], unidirecionais: [] });
  const conjuntos = { todos: novo(), mesmoGrupo: novo(), gruposDiferentes: novo() };
  pre.forEach((a, k) => {
    const b = pos[k];
    const destinos = [conjuntos.todos, grupoDe[a] === grupoDe[b] ? conjuntos.mesmoGrupo : conjuntos.gruposDiferentes];
    const inversa = indice.get(b * n + a);
    for (const c of destinos) {
      if (inversa === undefined) c.unidirecionais.push(w[k]);
      else if (a < b) {
        c.ida.push(w[k]);
        c.volta.push(w[inversa]);
        c.idaResidual.push(residuo(k));
        c.voltaResidual.push(residuo(inversa));
        c.forteIda.push(forte(k));
        c.forteVolta.push(forte(inversa));
      }
    }
  });
  const resumir = ({ ida, volta, idaResidual, voltaResidual, forteIda, forteVolta, unidirecionais }) => {
    const abaixo = ida.map((x, k) => x < 0.99 * teto && volta[k] < 0.99 * teto);
    const variam = Number.isFinite(pearson(ida, volta)); // com pesos iguais os resíduos são só arredondamento
    const fracao = (lista) => lista.filter(Boolean).length / lista.length;
    return {
      pares: ida.length,
      fracaoReciproca: ida.length / (ida.length + unidirecionais.length),
      correlacao: pearson(ida, volta),
      correlacaoSemTeto: pearson(ida.filter((_, k) => abaixo[k]), volta.filter((_, k) => abaixo[k])),
      correlacaoPorBloco: variam ? pearson(idaResidual, voltaResidual) : NaN,
      // pares fortes nos dois sentidos / o esperado se a força de cada sentido fosse independente
      fortesNosDois: variam ? fracao(forteIda.map((f, k) => f && forteVolta[k])) / (fracao(forteIda) * fracao(forteVolta)) : NaN,
      razao: media([...ida, ...volta]) / media(unidirecionais),
    };
  };
  const todos = resumir(conjuntos.todos);
  return { ...todos, mesmoGrupo: resumir(conjuntos.mesmoGrupo), gruposDiferentes: resumir(conjuntos.gruposDiferentes) };
}

// Correlação das contagens de spikes em bins para cada par de excitatórios. Devolve uma função
// (a, b) → r. Cada neurônio é padronizado (média 0, norma 1), e r vira um produto escalar.
function correlacoesDasRespostas(spikes, nExc, inicio, fim, larguraDoBin) {
  const nBins = Math.floor((fim - inicio) / larguraDoBin);
  const contagens = new Float64Array(nExc * nBins);
  for (let k = 0; k < spikes.length; k += 2) {
    const bin = Math.floor((spikes[k + 1] - inicio) / larguraDoBin);
    if (spikes[k] < nExc && bin >= 0 && bin < nBins) contagens[spikes[k] * nBins + bin]++;
  }
  const valido = new Uint8Array(nExc);
  for (let i = 0; i < nExc; i++) {
    const linhaI = contagens.subarray(i * nBins, (i + 1) * nBins);
    const m = media(linhaI);
    const norma = Math.sqrt(linhaI.reduce((s, c) => s + (c - m) ** 2, 0));
    if (norma === 0) continue;
    valido[i] = 1;
    for (let b = 0; b < nBins; b++) linhaI[b] = (linhaI[b] - m) / norma;
  }
  return (a, b) => {
    if (!valido[a] || !valido[b]) return NaN;
    let r = 0;
    for (let k = 0; k < nBins; k++) r += contagens[a * nBins + k] * contagens[b * nBins + k];
    return r;
  };
}

// Peso × semelhança das respostas, e peso dentro do mesmo grupo de entrada × entre grupos
function pesoESemelhanca(retrato, correlacao, grupoDe) {
  const comR = { pesos: [], r: [] };
  const mesmo = { pesos: [], r: [] };
  const diferente = { pesos: [], r: [] };
  retrato.pre.forEach((a, k) => {
    const b = retrato.pos[k];
    const r = correlacao(a, b);
    const destino = grupoDe[a] === grupoDe[b] ? mesmo : diferente;
    destino.pesos.push(retrato.w[k]);
    if (!Number.isFinite(r)) return;
    comR.pesos.push(retrato.w[k]);
    comR.r.push(r);
    destino.r.push(r);
  });
  return {
    correlacao: pearson(comR.pesos, comR.r),
    razaoGrupo: media(mesmo.pesos) / media(diferente.pesos),
    rMesmoGrupo: media(mesmo.r),
    rGruposDiferentes: media(diferente.r),
  };
}

// Taxas médias numa janela { de, ate, spikes }
function taxasDaJanela(rede, { de, ate, spikes }) {
  let spikesE = 0;
  for (let k = 0; k < spikes.length; k += 2) if (spikes[k] < rede.nExc) spikesE++;
  const segundos = (ate - de) / 1000;
  return { taxaE: spikesE / rede.nExc / segundos, taxaI: (spikes.length / 2 - spikesE) / rede.nInib / segundos };
}

// As medidas de pesos e respostas de um retrato numa janela
function medirJanela(rede, retrato, janela, larguraDoBin) {
  const grupoDe = grupoDosNeuronios(rede);
  const correlacao = correlacoesDasRespostas(janela.spikes, rede.nExc, janela.de, janela.ate, larguraDoBin);
  return {
    ...taxasDaJanela(rede, janela),
    pesos: estatisticasDePesos(retrato.w, rede.escala, rede.teto),
    reciprocidade: reciprocidade(retrato, grupoDe, rede.teto),
    semelhanca: pesoESemelhanca(retrato, correlacao, grupoDe),
  };
}

// Peso × respostas com os pesos do fim congelados. A correlação "de entrada" (sem recorrência E→E)
// é a que a entrada externa e a inibição produzem sozinhas; a "da rede" (com recorrência) soma a
// que os pesos E→E criam. Se os pesos só acompanham a entrada, r(w, entrada) dá conta de
// r(w, rede) e a parcial r(w, rede | entrada) fica perto de zero; se os pesos criam correlação,
// a parcial fica positiva. "ganho" é a correlação da rede menos a de entrada, par a par.
function medirCausalidade(rede, retrato, congelado, larguraDoBin) {
  const grupoDe = grupoDosNeuronios(rede);
  const janelas = { rede: congelado.comRecorrencia, entrada: congelado.semRecorrencia };
  const correlacao = {};
  for (const [nome, j] of Object.entries(janelas)) correlacao[nome] = correlacoesDasRespostas(j.spikes, rede.nExc, j.de, j.ate, larguraDoBin);
  const novo = () => ({ w: [], rede: [], entrada: [] });
  const conjuntos = { todos: novo(), mesmoGrupo: novo(), gruposDiferentes: novo() };
  retrato.pre.forEach((a, k) => {
    const b = retrato.pos[k];
    const rRede = correlacao.rede(a, b);
    const rEntrada = correlacao.entrada(a, b);
    if (!Number.isFinite(rRede) || !Number.isFinite(rEntrada)) return;
    for (const c of [conjuntos.todos, grupoDe[a] === grupoDe[b] ? conjuntos.mesmoGrupo : conjuntos.gruposDiferentes]) {
      c.w.push(retrato.w[k]);
      c.rede.push(rRede);
      c.entrada.push(rEntrada);
    }
  });
  const resumir = ({ w, rede: rRede, entrada: rEntrada }) => ({
    pares: w.length,
    wRede: pearson(w, rRede),
    wEntrada: pearson(w, rEntrada),
    entradaRede: pearson(rEntrada, rRede),
    parcial: correlacaoParcial(w, rRede, rEntrada),
    wGanho: pearson(
      w,
      rRede.map((r, k) => r - rEntrada[k]),
    ),
    respostaRede: media(rRede),
    respostaEntrada: media(rEntrada),
  });
  return {
    rede: taxasDaJanela(rede, janelas.rede),
    entrada: taxasDaJanela(rede, janelas.entrada),
    todos: resumir(conjuntos.todos),
    mesmoGrupo: resumir(conjuntos.mesmoGrupo),
    gruposDiferentes: resumir(conjuntos.gruposDiferentes),
  };
}

// Todas as medidas de pesos e respostas de um registro
function medirRegistro(registro) {
  const { rede, inicio, fim, congelado, experimento: e } = registro;
  return {
    inicio: inicio.janela ? medirJanela(rede, inicio, inicio.janela, e.larguraDoBin) : null,
    fim: medirJanela(rede, fim, fim.janela, e.larguraDoBin),
    causalidade: congelado ? medirCausalidade(rede, fim, congelado, e.larguraDoBin) : null,
  };
}

// As medidas de uma tabela: rótulo, como ler da medida e casas decimais
const medidasDoConectoma = [
  ["taxa E (Hz)", (m) => m.taxaE, 1],
  ["taxa I (Hz)", (m) => m.taxaI, 1],
  ["peso E→E médio / w_max", (m) => m.pesos.mediaRelativa, 3],
  ["CV dos pesos E→E", (m) => m.pesos.cv, 2],
  ["σ de ln w", (m) => m.pesos.sigmaLn, 2],
  ["assimetria de ln w (lognormal: 0)", (m) => m.pesos.assimetria, 2],
  ["curtose em excesso de ln w (lognormal: 0)", (m) => m.pesos.curtose, 2],
  ["KS: D de ln w × normal", (m) => m.pesos.ks, 3],
  ["KS: D crítico a 5%", (m) => m.pesos.ksCritico, 3],
  ["fração no teto", (m) => m.pesos.noTeto, 3],
  ["fração em zero", (m) => m.pesos.emZero, 3],
  ["r(w A→B, w B→A) nos pares recíprocos", (m) => m.reciprocidade.correlacao, 3],
  ["  mesmo grupo", (m) => m.reciprocidade.mesmoGrupo.correlacao, 3],
  ["  grupos diferentes", (m) => m.reciprocidade.gruposDiferentes.correlacao, 3],
  ["  sem pares com algum peso no teto", (m) => m.reciprocidade.correlacaoSemTeto, 3],
  ["  mesmo grupo, sem pares no teto", (m) => m.reciprocidade.mesmoGrupo.correlacaoSemTeto, 3],
  ["  descontando a média de cada bloco de grupos", (m) => m.reciprocidade.correlacaoPorBloco, 3],
  ["    mesmo grupo", (m) => m.reciprocidade.mesmoGrupo.correlacaoPorBloco, 3],
  ["    grupos diferentes", (m) => m.reciprocidade.gruposDiferentes.correlacaoPorBloco, 3],
  ["fortes nos dois sentidos / esperado (por bloco)", (m) => m.reciprocidade.fortesNosDois, 2],
  ["  mesmo grupo", (m) => m.reciprocidade.mesmoGrupo.fortesNosDois, 2],
  ["  grupos diferentes", (m) => m.reciprocidade.gruposDiferentes.fortesNosDois, 2],
  ["peso médio recíprocos / unidirecionais", (m) => m.reciprocidade.razao, 3],
  ["  mesmo grupo", (m) => m.reciprocidade.mesmoGrupo.razao, 3],
  ["  grupos diferentes", (m) => m.reciprocidade.gruposDiferentes.razao, 3],
  ["pares recíprocos no mesmo grupo (contagem)", (m) => m.reciprocidade.mesmoGrupo.pares, 0],
  ["r(peso, correlação das respostas)", (m) => m.semelhanca.correlacao, 3],
  ["peso médio mesmo grupo / grupos diferentes", (m) => m.semelhanca.razaoGrupo, 3],
  ["correlação das respostas, mesmo grupo", (m) => m.semelhanca.rMesmoGrupo, 3],
  ["correlação das respostas, grupos diferentes", (m) => m.semelhanca.rGruposDiferentes, 3],
];

// As medidas da causalidade: rótulo, como ler e casas decimais
const medidasDaCausalidade = [
  ["taxa E com recorrência (Hz)", (c) => c.rede.taxaE, 1],
  ["taxa E sem recorrência E→E (Hz)", (c) => c.entrada.taxaE, 1],
  ["taxa I com / sem recorrência (Hz)", (c) => c.rede.taxaI, 1, (c) => c.entrada.taxaI],
  ["correlação das respostas, com recorrência", (c) => c.todos.respostaRede, 3],
  ["correlação das respostas, só de entrada", (c) => c.todos.respostaEntrada, 3],
  ["  mesmo grupo: com / só de entrada", (c) => c.mesmoGrupo.respostaRede, 3, (c) => c.mesmoGrupo.respostaEntrada],
  ["  grupos diferentes: com / só de entrada", (c) => c.gruposDiferentes.respostaRede, 3, (c) => c.gruposDiferentes.respostaEntrada],
  ["r(peso, correlação com recorrência)", (c) => c.todos.wRede, 3],
  ["r(peso, correlação de entrada)", (c) => c.todos.wEntrada, 3],
  ["r(correlação de entrada, com recorrência)", (c) => c.todos.entradaRede, 3],
  ["r(peso, com recorrência | de entrada) parcial", (c) => c.todos.parcial, 3],
  ["r(peso, com recorrência − de entrada)", (c) => c.todos.wGanho, 3],
  ["mesmo grupo: r(peso, com recorrência)", (c) => c.mesmoGrupo.wRede, 3],
  ["mesmo grupo: r(peso, de entrada)", (c) => c.mesmoGrupo.wEntrada, 3],
  ["mesmo grupo: parcial", (c) => c.mesmoGrupo.parcial, 3],
  ["grupos diferentes: r(peso, com recorrência)", (c) => c.gruposDiferentes.wRede, 3],
  ["grupos diferentes: r(peso, de entrada)", (c) => c.gruposDiferentes.wEntrada, 3],
  ["grupos diferentes: parcial", (c) => c.gruposDiferentes.parcial, 3],
];

// "média ± desvio" entre sementes, ignorando NaN; "—" se nenhuma semente tem o valor
function resumoEntreSementes(valores, casas) {
  const validos = valores.filter(Number.isFinite);
  if (validos.length === 0) return "—";
  return `${media(validos).toFixed(casas)} ± ${desvioPadrao(validos).toFixed(casas)}`;
}

// --- Medidas da fiação E→E (Fase 2) ---------------------------------------------------

// As 16 tríades de Holland & Leinhardt, cada uma por um representante com os nós A = 0, B = 1 e
// C = 2 (arestas [de, para]). A tabela dos 64 códigos possíveis sai de permutar os representantes.
const triades = [
  ["003", []],
  ["012", [[0, 1]]],
  ["102", [[0, 1], [1, 0]]],
  ["021D", [[1, 0], [1, 2]]], // A ← B → C
  ["021U", [[0, 1], [2, 1]]], // A → B ← C
  ["021C", [[0, 1], [1, 2]]], // A → B → C
  ["111D", [[0, 1], [1, 0], [2, 1]]], // A ↔ B ← C
  ["111U", [[0, 1], [1, 0], [1, 2]]], // A ↔ B → C
  ["030T", [[0, 1], [2, 1], [0, 2]]], // A → B ← C, A → C
  ["030C", [[1, 0], [2, 1], [0, 2]]], // ciclo A → C → B → A
  ["201", [[0, 1], [1, 0], [1, 2], [2, 1]]], // A ↔ B ↔ C
  ["120D", [[1, 0], [1, 2], [0, 2], [2, 0]]], // A ← B → C, A ↔ C
  ["120U", [[0, 1], [2, 1], [0, 2], [2, 0]]], // A → B ← C, A ↔ C
  ["120C", [[0, 1], [1, 2], [0, 2], [2, 0]]], // A → B → C, A ↔ C
  ["210", [[0, 1], [1, 2], [2, 1], [0, 2], [2, 0]]], // A → B ↔ C, A ↔ C
  ["300", [[0, 1], [1, 0], [1, 2], [2, 1], [0, 2], [2, 0]]],
];

// Código de 6 bits de uma tríade (x, y, z): x→y, y→x, x→z, z→x, y→z, z→y
const bitDaAresta = { "0,1": 0, "1,0": 1, "0,2": 2, "2,0": 3, "1,2": 4, "2,1": 5 };
const tabelaDeTriades = (() => {
  const tabela = new Int8Array(64).fill(-1);
  const permutacoes = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
  triades.forEach(([, arestas], classe) => {
    for (const p of permutacoes) {
      const codigo = arestas.reduce((c, [a, b]) => c | (1 << bitDaAresta[`${p[a]},${p[b]}`]), 0);
      if (tabela[codigo] !== -1 && tabela[codigo] !== classe) throw new Error(`tríade ambígua: código ${codigo}`);
      tabela[codigo] = classe;
    }
  });
  if (tabela.includes(-1)) throw new Error("tabela de tríades incompleta");
  return tabela;
})();

// Matriz de adjacência E→E de um retrato: adj[i·nE + j] = 1 se há sinapse de i para j
function adjacenciaEE(retrato, nE) {
  const adj = new Uint8Array(nE * nE);
  retrato.pre.forEach((i, k) => (adj[i * nE + retrato.pos[k]] = 1));
  return adj;
}

// Pares recíprocos contra o acaso: numa rede ao acaso de densidade p há p²·nE(nE − 1)/2 deles
function reciprocosContraOAcaso(adj, nE) {
  let arestas = 0;
  let reciprocos = 0;
  for (let i = 0; i < nE; i++) {
    for (let j = i + 1; j < nE; j++) {
      const ida = adj[i * nE + j];
      const volta = adj[j * nE + i];
      arestas += ida + volta;
      if (ida && volta) reciprocos++;
    }
  }
  const p = arestas / (nE * (nE - 1));
  return { arestas, reciprocos, razao: reciprocos / ((p * p * nE * (nE - 1)) / 2) };
}

// Agrupamento médio da rede não direcionada (vizinhos se há sinapse em qualquer sentido): para cada
// neurônio, a fração dos pares de vizinhos que também são vizinhos entre si
function agrupamento(adj, nE) {
  const liga = (i, j) => adj[i * nE + j] || adj[j * nE + i];
  let soma = 0;
  let contados = 0;
  for (let i = 0; i < nE; i++) {
    const vizinhos = [];
    for (let j = 0; j < nE; j++) if (j !== i && liga(i, j)) vizinhos.push(j);
    const k = vizinhos.length;
    if (k < 2) continue;
    let ligados = 0;
    for (let a = 0; a < k; a++) for (let b = a + 1; b < k; b++) if (liga(vizinhos[a], vizinhos[b])) ligados++;
    soma += ligados / ((k * (k - 1)) / 2);
    contados++;
  }
  return soma / contados;
}

// Contagem das 16 tríades em todas as trincas de neurônios
function censoDeTriades(adj, nE) {
  const contagem = new Float64Array(16);
  for (let i = 0; i < nE; i++) {
    for (let j = i + 1; j < nE; j++) {
      const ij = adj[i * nE + j] | (adj[j * nE + i] << 1);
      for (let k = j + 1; k < nE; k++) {
        const codigo = ij | (adj[i * nE + k] << 2) | (adj[k * nE + i] << 3) | (adj[j * nE + k] << 4) | (adj[k * nE + j] << 5);
        contagem[tabelaDeTriades[codigo]]++;
      }
    }
  }
  return contagem;
}

// Modelos nulos. Os pares não ordenados (i < j) são sorteados sem repetição.
function sortearPares(nE, quantos) {
  const total = (nE * (nE - 1)) / 2;
  const indices = new Int32Array(total).map((_, k) => k);
  for (let k = 0; k < quantos; k++) {
    const r = k + Math.floor(aleatorio() * (total - k));
    [indices[k], indices[r]] = [indices[r], indices[k]];
  }
  // índice k → par (i, j) com i < j
  const pares = [];
  const inicioDaLinha = (i) => i * nE - (i * (i + 1)) / 2;
  for (let k = 0; k < quantos; k++) {
    let i = 0;
    while (inicioDaLinha(i + 1) <= indices[k]) i++;
    pares.push([i, i + 1 + indices[k] - inicioDaLinha(i)]);
  }
  return pares;
}

// Mantém o número de pares recíprocos e o de unidirecionais (o modelo nulo de Song et al., 2005);
// com reciprocosAoAcaso, mantém só o número de arestas (rede ao acaso)
function redeNula(adj, nE, { reciprocosAoAcaso = false } = {}) {
  const { arestas, reciprocos } = reciprocosContraOAcaso(adj, nE);
  const nula = new Uint8Array(nE * nE);
  if (reciprocosAoAcaso) {
    let colocadas = 0;
    while (colocadas < arestas) {
      const i = Math.floor(aleatorio() * nE);
      const j = Math.floor(aleatorio() * nE);
      if (i !== j && !nula[i * nE + j]) {
        nula[i * nE + j] = 1;
        colocadas++;
      }
    }
    return nula;
  }
  const unidirecionais = arestas - 2 * reciprocos;
  sortearPares(nE, reciprocos + unidirecionais).forEach(([i, j], k) => {
    if (k < reciprocos) {
      nula[i * nE + j] = 1;
      nula[j * nE + i] = 1;
    } else if (aleatorio() < 0.5) nula[i * nE + j] = 1;
    else nula[j * nE + i] = 1;
  });
  return nula;
}

// Nulos por blocos: cada bloco (grupo de origem → grupo de destino) mantém o seu número de arestas,
// então a densidade dentro e entre grupos fica igual à observada. Com manterReciprocos, cada par
// de grupos mantém também o número de pares recíprocos e de unidirecionais em cada sentido.
function redeNulaPorBlocos(adj, nE, grupos, { manterReciprocos = false } = {}) {
  const nula = new Uint8Array(nE * nE);
  grupos.forEach((A, ga) => {
    grupos.forEach((B, gb) => {
      if (manterReciprocos) {
        if (gb < ga) return;
        // pares não ordenados {i, j}, i em A e j em B (i < j dentro do mesmo grupo)
        const pares = [];
        for (const i of A) for (const j of B) if (ga !== gb || i < j) pares.push([i, j]);
        let mutuos = 0;
        let ida = 0;
        let volta = 0;
        for (const [i, j] of pares) {
          const f = adj[i * nE + j];
          const t = adj[j * nE + i];
          if (f && t) mutuos++;
          else if (f) ida++;
          else if (t) volta++;
        }
        embaralhar(pares);
        pares.forEach(([i, j], k) => {
          if (k < mutuos) nula[i * nE + j] = nula[j * nE + i] = 1;
          else if (k < mutuos + ida) nula[i * nE + j] = 1;
          else if (k < mutuos + ida + volta) nula[j * nE + i] = 1;
        });
        return;
      }
      // pares ordenados i → j, i em A e j em B
      const pares = [];
      for (const i of A) for (const j of B) if (i !== j) pares.push([i, j]);
      const arestas = pares.reduce((total, [i, j]) => total + adj[i * nE + j], 0);
      embaralhar(pares);
      for (let k = 0; k < arestas; k++) nula[pares[k][0] * nE + pares[k][1]] = 1;
    });
  });
  return nula;
}

// Pares recíprocos esperados se cada bloco fosse ao acaso com a sua própria densidade
function reciprocosEsperadosPorBlocos(adj, nE, grupos) {
  let esperado = 0;
  grupos.forEach((A, ga) => {
    grupos.forEach((B, gb) => {
      if (gb < ga) return;
      const densidade = (X, Y) => {
        let arestas = 0;
        for (const i of X) for (const j of Y) if (i !== j) arestas += adj[i * nE + j];
        return arestas / (X.length * Y.length - (X === Y ? X.length : 0));
      };
      const pares = ga === gb ? (A.length * (A.length - 1)) / 2 : A.length * B.length;
      esperado += pares * densidade(A, B) * densidade(B, A);
    });
  });
  return esperado;
}

// Nulos de Maslov & Sneppen (2002): trocas de arestas que mantêm o grau de entrada e o de saída de
// cada neurônio. Cada troca sorteia duas arestas a→b e c→d e as troca por a→d e c→b, se isso não
// cria laço nem aresta repetida; `trocasPorAresta` trocas aceitas por aresta misturam a rede.
// Com manterReciprocos (como no mfinder de Milo et al., 2002), unidirecionais e pares recíprocos
// são trocados em separado: uma troca de unidirecionais não pode criar recíprocos (a→d só entra
// se d→a não existe), e os pares recíprocos trocam de parceiro entre si. Assim cada neurônio
// mantém também o seu número de recíprocos, e o total de recíprocos não muda.
function redeNulaPorGrau(adj, nE, { manterReciprocos = false, trocasPorAresta = 10 } = {}) {
  const nula = adj.slice();
  const tem = (i, j) => nula[i * nE + j] === 1;
  const ligar = (i, j, valor) => (nula[i * nE + j] = valor);
  const trocar = (arestas, tentar, semSentido) => {
    const meta = trocasPorAresta * arestas.length;
    let feitas = 0;
    for (let tentativa = 0; feitas < meta && tentativa < 20 * meta; tentativa++) {
      const x = Math.floor(aleatorio() * arestas.length);
      const y = Math.floor(aleatorio() * arestas.length);
      if (x === y) continue;
      const [a, b] = arestas[x];
      let [c, d] = arestas[y];
      if (semSentido && aleatorio() < 0.5) [c, d] = [d, c]; // um par recíproco pode trocar pelos dois lados
      if (a === c || b === d || !tentar(a, b, c, d)) continue;
      arestas[x] = [a, d];
      arestas[y] = [c, b];
      feitas++;
    }
  };
  const simples = [];
  const pares = [];
  for (let i = 0; i < nE; i++) {
    for (let j = 0; j < nE; j++) {
      if (!tem(i, j)) continue;
      if (!manterReciprocos || !tem(j, i)) simples.push([i, j]);
      else if (i < j) pares.push([i, j]);
    }
  }
  trocar(simples, (a, b, c, d) => {
    if (a === d || c === b || tem(a, d) || tem(c, b)) return false;
    if (manterReciprocos && (tem(d, a) || tem(b, c))) return false;
    ligar(a, b, 0);
    ligar(c, d, 0);
    ligar(a, d, 1);
    ligar(c, b, 1);
    return true;
  });
  trocar(
    pares,
    (a, b, c, d) => {
      if (a === d || c === b || tem(a, d) || tem(d, a) || tem(c, b) || tem(b, c)) return false;
      for (const [i, j, valor] of [[a, b, 0], [c, d, 0], [a, d, 1], [c, b, 1]]) {
        ligar(i, j, valor);
        ligar(j, i, valor);
      }
      return true;
    },
    true,
  );
  return nula;
}

// Os modelos nulos da fiação:
//   aoAcaso: o mesmo número de arestas
//   mantendoReciprocos: os mesmos números de pares recíprocos e unidirecionais (Song et al., 2005)
//   porBlocos: as mesmas densidades dentro e entre grupos
//   porBlocosComReciprocos: e, em cada par de grupos, os mesmos recíprocos e unidirecionais
//   grau: o grau de entrada e o de saída de cada neurônio (Maslov-Sneppen)
//   grauComReciprocos: e o número de recíprocos de cada neurônio
const nulosDaFiacao = {
  aoAcaso: (adj, nE) => redeNula(adj, nE, { reciprocosAoAcaso: true }),
  mantendoReciprocos: (adj, nE) => redeNula(adj, nE),
  porBlocos: (adj, nE, grupos) => redeNulaPorBlocos(adj, nE, grupos),
  porBlocosComReciprocos: (adj, nE, grupos) => redeNulaPorBlocos(adj, nE, grupos, { manterReciprocos: true }),
  grau: (adj, nE) => redeNulaPorGrau(adj, nE),
  grauComReciprocos: (adj, nE) => redeNulaPorGrau(adj, nE, { manterReciprocos: true }),
};

// Todas as medidas da fiação de um retrato, com `amostras` redes de cada nulo para comparar:
// razão observado/média dos nulos e z = (observado − média)/desvio
function medirFiacao(retrato, rede, amostras = 20) {
  const nE = rede.nExc;
  const adj = adjacenciaEE(retrato, nE);
  const nulas = Object.fromEntries(
    Object.entries(nulosDaFiacao).map(([tipo, gerar]) => [
      tipo,
      Array.from({ length: amostras }, () => {
        const nula = gerar(adj, nE, rede.grupos);
        return { agrupamento: agrupamento(nula, nE), triades: censoDeTriades(nula, nE), reciprocos: reciprocosContraOAcaso(nula, nE).reciprocos };
      }),
    ]),
  );
  const comparar = (observado, valoresNulos) => {
    const m = media(valoresNulos);
    const dp = desvioPadrao(valoresNulos);
    return { razao: observado / m, z: dp > 0 ? (observado - m) / dp : NaN };
  };
  const porNulo = (observado, ler) => Object.fromEntries(Object.keys(nulosDaFiacao).map((tipo) => [tipo, comparar(observado, nulas[tipo].map(ler))]));
  const reciprocos = reciprocosContraOAcaso(adj, nE);
  const observado = agrupamento(adj, nE);
  const triadesObservadas = censoDeTriades(adj, nE);
  return {
    reciprocos: {
      ...reciprocos,
      razaoPorBlocos: reciprocos.reciprocos / reciprocosEsperadosPorBlocos(adj, nE, rede.grupos),
      grau: comparar(reciprocos.reciprocos, nulas.grau.map((n) => n.reciprocos)),
    },
    agrupamento: { observado, ...porNulo(observado, (n) => n.agrupamento) },
    triades: triades.map((_, c) => porNulo(triadesObservadas[c], (n) => n.triades[c])),
  };
}

// Motivos: tríades com z ≥ limiar (antimotivos: z ≤ −limiar) contra os dois nulos de grau em
// todas as sementes. Devolve os nomes, marcando com * as que também passam no nulo por blocos com
// recíprocos.
function motivosDaFiacao(fiacoes, limiar = 3) {
  const passa = (c, tipo, sinal) => fiacoes.every((f) => sinal * f.triades[c][tipo].z >= limiar);
  const lista = (sinal) =>
    triades
      .map(([nome], c) => [nome, c])
      .filter(([, c]) => c >= 3 && passa(c, "grau", sinal) && passa(c, "grauComReciprocos", sinal))
      .map(([nome, c]) => (passa(c, "porBlocosComReciprocos", sinal) ? `${nome}*` : nome));
  return { motivos: lista(1), antimotivos: lista(-1) };
}

// --- Configurações, análise e linha de comando -----------------------------------------

// Fase 1: os spikes compartilhados; teste extra, Fase 2 e testes de regra: também as rajadas
const entradasDoConectoma = {
  compartilhada: { fracaoCorrelacionada: 0.2, rajadas: null },
  rajadas: { fracaoCorrelacionada: 0, rajadas: { taxaHz: 0.5, duracao: 150, entradaHz: 3000 } },
};

// Fase 2: a cada 10 s, as 0,5% de sinapses E→E mais fracas (com pelo menos 60 s) são trocadas por
// sinapses ao acaso que nascem com metade do peso mediano (~45% de troca em 900 s). Com 2% e
// nascimento na mediana, a troca era mais rápida que a diferenciação dos pesos e apagava a estrutura.
const estruturalDoConectoma = { intervalo: 10000, fracao: 0.005, idadeMinima: 60000, pesoInicial: 0.5 };

// Teste da lognormal: teto E→E 4× maior (a escala da LTP não muda) e ruído multiplicativo
const variantesDaLognormal = {
  teto: { fatorTeto: 4, ruidoMultiplicativo: 0 },
  "ruido-0.03": { fatorTeto: 4, ruidoMultiplicativo: 0.03 },
  "ruido-0.1": { fatorTeto: 4, ruidoMultiplicativo: 0.1 },
};

const lerArgumento = (nome, padrao) => {
  const argumento = process.argv.find((a) => a.startsWith(`--${nome}=`));
  return argumento ? argumento.slice(nome.length + 3) : padrao;
};

function imprimirMedidasDePesos(titulo, medidas) {
  console.log(`\n${titulo}: média ± desvio entre ${medidas.length} sementes, início → fim`);
  for (const [rotulo, ler, casas] of medidasDoConectoma) {
    const inicio = resumoEntreSementes(medidas.map((m) => (m.inicio ? ler(m.inicio) : NaN)), casas);
    const fim = resumoEntreSementes(medidas.map((m) => ler(m.fim)), casas);
    linha(rotulo, `${inicio.padStart(17)}  →  ${fim}`);
  }
}

function imprimirCausalidade(condicao, causalidades) {
  console.log(`\n${condicao}, pesos do fim congelados: 20 s com recorrência E→E e 20 s sem, com a mesma entrada externa`);
  for (const [rotulo, ler, casas, lerSegundo] of medidasDaCausalidade) {
    const valor = resumoEntreSementes(causalidades.map(ler), casas);
    linha(rotulo, lerSegundo ? `${valor} / ${resumoEntreSementes(causalidades.map(lerSegundo), casas)}` : valor);
  }
}

function imprimirFiacao(condicao, registros) {
  const medir = (registro, momento) => {
    semear(registro.semente * 10 + (momento === "inicio" ? 1 : 2)); // nulos reproduzíveis
    return medirFiacao(registro[momento], registro.rede);
  };
  const fiacoes = registros.map((r) => medir(r, "fim"));
  const iniciais = registros.map((r) => medir(r, "inicio"));
  const resumo = (ler, casas = 2) => resumoEntreSementes(fiacoes.map(ler), casas);
  const zMedio = (ler) => {
    const z = media(fiacoes.map(ler).filter(Number.isFinite));
    return Number.isFinite(z) ? z.toFixed(1) : "—";
  };
  console.log(`\n${condicao}, fiação no fim (no início ela é ao acaso)`);
  linha("pares recíprocos / esperado ao acaso", resumo((f) => f.reciprocos.razao));
  linha("pares recíprocos / esperado por blocos", resumo((f) => f.reciprocos.razaoPorBlocos));
  linha("pares recíprocos / nulo de grau", `${resumo((f) => f.reciprocos.grau.razao, 3)} (z ${zMedio((f) => f.reciprocos.grau.z)})`);
  linha("agrupamento", resumo((f) => f.agrupamento.observado, 4));
  for (const [rotulo, tipo] of [
    ["agrupamento / rede ao acaso", "aoAcaso"],
    ["agrupamento / nulo com os mesmos recíprocos", "mantendoReciprocos"],
    ["agrupamento / nulo por blocos", "porBlocos"],
    ["agrupamento / nulo por blocos com recíprocos", "porBlocosComReciprocos"],
    ["agrupamento / nulo de grau", "grau"],
    ["agrupamento / nulo de grau com recíprocos", "grauComReciprocos"],
  ]) {
    linha(rotulo, `${resumo((f) => f.agrupamento[tipo].razao, 3)} (z ${zMedio((f) => f.agrupamento[tipo].z)})`);
  }
  const colunas = [
    ["Song", "mantendoReciprocos"],
    ["blocos+recíp.", "porBlocosComReciprocos"],
    ["grau", "grau"],
    ["grau+recíp.", "grauComReciprocos"],
  ];
  console.log(`  tríades, observado / nulo e z médio: ${colunas.map(([nome]) => nome).join(" · ")}`);
  triades.forEach(([nome], c) => {
    if (c < 3) return; // 003, 012 e 102 só dependem das contagens de pares, que os nulos mantêm
    const celula = (tipo) => {
      const razoes = fiacoes.map((f) => f.triades[c][tipo].razao);
      return `${media(razoes).toFixed(2)}±${desvioPadrao(razoes).toFixed(2)} z${zMedio((f) => f.triades[c][tipo].z)}`.padEnd(19);
    };
    linha(`  ${nome}`, colunas.map(([, tipo]) => celula(tipo)).join(" "));
  });
  const nomes = (lista) => (lista.length ? lista.join(", ") : "nenhum");
  const fim = motivosDaFiacao(fiacoes);
  const inicio = motivosDaFiacao(iniciais);
  console.log("  motivos: z ≥ 3 contra os dois nulos de grau em todas as sementes (* também contra blocos+recíp.)");
  linha("  no fim: motivos", nomes(fim.motivos));
  linha("  no fim: antimotivos", nomes(fim.antimotivos));
  linha("  fiação inicial ao acaso (esperado: nenhum)", `motivos: ${nomes(inicio.motivos)} · antimotivos: ${nomes(inicio.antimotivos)}`);
}

// Refaz todas as medidas a partir dos registros, uma condição por vez
function analisarRegistros(registros) {
  const ordem = Object.keys(condicoesDoConectoma);
  const condicoes = [...new Set(registros.map((r) => r.condicao))].sort((a, b) => ordem.indexOf(a) - ordem.indexOf(b));
  for (const condicao of condicoes) {
    const lista = registros.filter((r) => r.condicao === condicao).sort((a, b) => a.semente - b.semente);
    const medidas = lista.map(medirRegistro);
    imprimirMedidasDePesos(`${condicao} (${lista[0].fim.pre.length} sinapses E→E), sementes ${lista.map((r) => r.semente).join(", ")}`, medidas);
    if (medidas.every((m) => m.causalidade)) imprimirCausalidade(condicao, medidas.map((m) => m.causalidade));
    if (lista[0].experimento.estrutural) imprimirFiacao(condicao, lista);
  }
}

// Avaliação para a regra de Clopath na rede: o mesmo protocolo de pares (5 pares a cada
// frequência, |Δt| = 10 ms, spike pós forçado por 2 ms a 33 mV) em vários neurônios, com a regra do
// artigo (ū sem atraso) e com a da implementação de referência (ū com 4 ms de atraso). A regra
// lê a voltagem; o neurônio serve se as curvas de Δw × frequência saem como no AdEx de Clopath.
function comSpikeTravado(criar, integrar, reiniciar) {
  const { vPico, tTravado } = parametrosAdExClopath;
  return {
    criar: () => ({ ...criar(), travado: 0 }),
    forcar: (s) => Object.assign(s, { v: vPico, travado: tTravado }),
    passo: (s, dt) => {
      if (s.travado <= 0) return integrar(s, dt);
      s.travado -= dt;
      if (s.travado <= 1e-9) reiniciar(s);
    },
  };
}

const neuroniosDoTesteDeClopath = {
  "AdEx de Clopath": {
    criar: criarAdExClopath,
    forcar: (s) => {
      const p = parametrosAdExClopath;
      Object.assign(s, { v: p.vPico, travado: p.tTravado, w: s.w + p.b, z: p.iSp, vT: p.vTMax });
    },
    passo: (s, dt) => passoAdExClopath(s, parametrosAdExClopath, 0, dt),
  },
  "AdEx sem pós-potencial (11)": comSpikeTravado(
    criarAdEx,
    (s, dt) => passoAdEx(s, parametrosAdEx, 0, dt),
    (s) => Object.assign(s, { v: parametrosAdEx.vReset, w: s.w + parametrosAdEx.b }),
  ),
  ...Object.fromEntries(
    ["regular", "tagarela"].map((tipo) => {
      const izh = tiposIzhikevich[tipo];
      const neuronio = comSpikeTravado(
        () => criarIzhikevich(izh, -70),
        (s, dt) => passoIzhikevich(s, izh, 0, dt),
        (s) => Object.assign(s, { v: izh.c, u: s.u + izh.d }),
      );
      return [`Izhikevich ${tipo}`, neuronio];
    }),
  ),
};

// Δw/w₀ depois de `pares` pares com Δt = delta (pós − pré) na frequência dada
function protocoloClopathNoNeuronio(modelo, delta, frequenciaHz, { pares = 5, dt = 0.1, atraso = 4 } = {}) {
  const p = parametrosClopath;
  const periodo = 1000 / frequenciaHz;
  const inicio = 1000; // ms para o neurônio chegar ao repouso
  const passosPre = new Set();
  const passosPos = new Set();
  for (let k = 0; k < pares; k++) {
    passosPre.add(Math.round((inicio + k * periodo) / dt));
    passosPos.add(Math.round((inicio + k * periodo + delta) / dt));
  }
  const s = modelo.criar();
  const comprimento = Math.max(1, Math.round(atraso / dt));
  const anel = Array.from({ length: comprimento }, () => [p.thetaMenos, p.thetaMenos]);
  let uMenos = s.v;
  let uMais = s.v;
  let xBarra = 0;
  const w0 = 0.5;
  let w = w0;
  const total = Math.round((inicio + pares * periodo + 200) / dt);
  for (let passo = 0; passo < total; passo++) {
    if (passosPos.has(passo)) modelo.forcar(s);
    else modelo.passo(s, dt);
    const u = s.v;
    const pre = passosPre.has(passo);
    const [menosAtrasado, maisAtrasado] = atraso > 0 ? anel[passo % comprimento] : [uMenos, uMais];
    if (passo * dt >= inicio - 50) {
      if (pre) w -= p.aLTD * Math.max(0, menosAtrasado - p.thetaMenos);
      w += dt * p.aLTP * xBarra * Math.max(0, u - p.thetaMais) * Math.max(0, maisAtrasado - p.thetaMenos);
    }
    anel[passo % comprimento] = [uMenos, uMais];
    uMenos += (dt / p.tauMenos) * (u - uMenos);
    uMais += (dt / p.tauMais) * (u - uMais);
    xBarra += -(dt / p.tauX) * xBarra + (pre ? 1 / p.tauX : 0);
  }
  return (w - w0) / w0;
}

function avaliarNeuronioDeClopath() {
  const frequencias = [0.1, 10, 20, 30, 40, 50];
  const porcento = (x) => `${(100 * x).toFixed(1)}%`;
  for (const [titulo, atraso] of [
    ["regra do artigo (ū sem atraso)", 0],
    ["implementação de referência (ū com 4 ms de atraso)", 4],
  ]) {
    console.log(`\nClopath, ${titulo}: Δw/w₀ após 5 pares, pré→pós +10 ms / pós→pré −10 ms`);
    linha("", frequencias.map((f) => `${f} Hz`.padStart(14)).join(""));
    for (const [nome, modelo] of Object.entries(neuroniosDoTesteDeClopath)) {
      const celulas = frequencias.map((f) => {
        const ida = protocoloClopathNoNeuronio(modelo, 10, f, { atraso });
        const volta = protocoloClopathNoNeuronio(modelo, -10, f, { atraso });
        return `${porcento(ida)}/${porcento(volta)}`.padStart(14);
      });
      linha(nome, celulas.join(""));
    }
  }
}

// --- Replicação da rede de Clopath et al. (2010, fig. 5) --------------------------------------
// Antes de levar a regra para a nossa rede, ela precisa funcionar no cenário publicado. Este é o
// exemplo clopath_synapse_small_network.py do NEST, que adapta a figura 5 do artigo:
//   10 excitatórios e 3 inibitórios aeif_psc_delta_clopath; sinapses delta (cada spike soma w mV
//   na voltagem do alvo, um passo depois); dt = 0,1 ms; 10 s
//   500 entradas Poisson: a entrada j dispara a 1,75 × 30·exp(−(j − μ)²/(2·10²)) Hz, e o centro μ
//   salta a cada 100 ms para uma de 10 posições (25, 75, ..., 475)
//   entradas → E: regra de Clopath, w inicial U(0,5; 2), w_max 3; E → E: todos com todos, regra de
//   Clopath, w inicial 0,25, w_max 0,75; entradas → I: fixas, U(0; 0,5); E → I: 8 entradas por
//   inibitório, peso 1; I → E: 6 saídas por inibitório, peso 1 (positivo, como no exemplo)
//   regra: A_LTP 8·10⁻⁶ e A_LTD 14·10⁻⁶ por mV de peso; LTD homeostática com ū̄ = ū₋ filtrada em
//   500 ms, em mV absolutos (como no NEST), e u_ref² = 60²; ū₋ e ū₊ com 5 ms de atraso
// Variantes do neurônio: o do exemplo do NEST (b de 0,0805 pA, V_peak 20 mV), o do código MATLAB
// dos autores no ModelDB 144566 (limiar sobe para −30,4 mV, reset em −49,5 mV) e o que o teste em
// rede usou (os padrões do NEST com b = 80,5 pA e detecção em 33 mV).
const replicacaoDeClopath = {
  nExc: 10,
  nInib: 3,
  nEntradas: 500,
  dt: 0.1,
  segundos: 10,
  amplitude: 30,
  sigma: 10,
  fatorDaTaxa: 1.75,
  intervalo: 100,
  pesoEntradaE: [0.5, 2],
  tetoEntradaE: 3,
  pesoEE: 0.25,
  tetoEE: 0.75,
  pesoEntradaI: [0, 0.5],
  pesoEI: 1,
  entradasPorI: 8,
  pesoIE: 1,
  saidasPorI: 6,
  regra: { ...parametrosClopath, aLTP: 8e-6, aLTD: 14e-6, tauMedia: 500, uRef2: 60 ** 2, atraso: 5 },
};

const neuroniosDaReplicacao = {
  "exemplo do NEST": { ...parametrosAdExClopath, b: 0.0805, vDisparo: 20 },
  "código MATLAB dos autores": { ...parametrosAdExClopath, b: 0.0805, vDisparo: 20, vTMax: -30.4, vReset: -49.5 },
  "o do teste em rede (4b)": parametrosAdExClopath,
};

// Uma rede de Clopath. Devolve os pesos E→E do fim, os de entrada → E e as taxas.
function simularRedeDeClopath(semente, neuronio, r = replicacaoDeClopath) {
  semear(semente);
  const p = r.regra;
  const { nExc, nInib, nEntradas, dt } = r;
  const n = nExc + nInib;
  const uniforme = ([a, b]) => a + (b - a) * aleatorio();
  const neuronios = Array.from({ length: n }, () => ({ ...criarAdExClopath(neuronio), v: -60 + 25 * gaussiana() }));
  const wEntrada = Array.from({ length: nExc }, () => Float64Array.from({ length: nEntradas }, () => uniforme(r.pesoEntradaE)));
  const wEntradaI = Array.from({ length: nInib }, () => Float64Array.from({ length: nEntradas }, () => uniforme(r.pesoEntradaI)));
  const wEE = Array.from({ length: nExc }, (_, i) => Float64Array.from({ length: nExc }, (_, j) => (i === j ? 0 : r.pesoEE))); // [pré][pós]
  const sortear = (quantos) => embaralhar(Array.from({ length: nExc }, (_, i) => i)).slice(0, quantos);
  const alvosEI = Array.from({ length: nExc }, () => []);
  for (let k = 0; k < nInib; k++) for (const i of sortear(r.entradasPorI)) alvosEI[i].push(k);
  const alvosIE = Array.from({ length: nInib }, () => sortear(r.saidasPorI));
  // regra: ū₋, ū₊ e ū̄ por excitatório, com anéis para o atraso; x̄ por neurônio pré
  const comprimento = Math.round(p.atraso / dt);
  const cheio = (valor) => Array.from({ length: nExc }, () => new Float64Array(comprimento).fill(valor));
  const [anelMenos, anelMais] = [cheio(neuronio.eL), cheio(neuronio.eL)];
  const uMenos = new Float64Array(nExc).fill(neuronio.eL);
  const uMais = new Float64Array(nExc).fill(neuronio.eL);
  const media = new Float64Array(nExc).fill(neuronio.eL);
  const uMenosAtrasado = new Float64Array(nExc).fill(neuronio.eL);
  const xEntrada = new Float64Array(nEntradas);
  const xExc = new Float64Array(nExc);
  const decaiX = Math.exp(-dt / p.tauX);
  const ltd = (i) => (uMenosAtrasado[i] > p.thetaMenos ? (p.aLTD * media[i] ** 2 * (uMenosAtrasado[i] - p.thetaMenos)) / p.uRef2 : 0);
  const somar = (alvo, w) => {
    if (neuronios[alvo].travado <= 0) neuronios[alvo].v += w; // durante o spike travado a entrada não conta
  };
  const taxas = new Float64Array(nEntradas);
  const spikes = new Float64Array(n);
  let chegando = { entradas: [], exc: [], inib: [] };
  let posicao = 0;
  const passos = Math.round((r.segundos * 1000) / dt);
  const passosPorIntervalo = Math.round(r.intervalo / dt);
  for (let passo = 0; passo < passos; passo++) {
    if (passo % passosPorIntervalo === 0) {
      const mu = 25 + Math.floor(aleatorio() * 10) * 50;
      for (let j = 0; j < nEntradas; j++) taxas[j] = (r.fatorDaTaxa * r.amplitude * Math.exp(-((j - mu) ** 2) / (2 * r.sigma ** 2)) * dt) / 1000;
    }
    // os spikes do passo anterior chegam agora (o atraso de 0,1 ms do exemplo), com a LTD de Clopath
    for (const j of chegando.entradas) {
      for (let i = 0; i < nExc; i++) {
        somar(i, wEntrada[i][j]);
        wEntrada[i][j] = Math.max(0, wEntrada[i][j] - ltd(i));
      }
      for (let k = 0; k < nInib; k++) somar(nExc + k, wEntradaI[k][j]);
      xEntrada[j] += 1 / p.tauX;
    }
    for (const i of chegando.exc) {
      for (let m = 0; m < nExc; m++) {
        if (m === i) continue;
        somar(m, wEE[i][m]);
        wEE[i][m] = Math.max(0, wEE[i][m] - ltd(m));
      }
      for (const k of alvosEI[i]) somar(nExc + k, r.pesoEI);
      xExc[i] += 1 / p.tauX;
    }
    for (const k of chegando.inib) for (const m of alvosIE[k]) somar(m, r.pesoIE);
    const novos = { entradas: [], exc: [], inib: [] };
    for (let i = 0; i < n; i++) {
      if (!passoAdExClopath(neuronios[i], neuronio, 0, dt)) continue;
      spikes[i]++;
      (i < nExc ? novos.exc : novos.inib).push(i < nExc ? i : i - nExc);
    }
    // LTP contínua nos excitatórios com u > θ₊, depois os filtros andam
    for (let i = 0; i < nExc; i++) {
      const u = neuronios[i].v;
      const maisAtrasado = anelMais[i][posicao];
      uMenosAtrasado[i] = anelMenos[i][posicao];
      if (u > p.thetaMais && maisAtrasado > p.thetaMenos) {
        const fator = dt * p.aLTP * (u - p.thetaMais) * (maisAtrasado - p.thetaMenos);
        for (let j = 0; j < nEntradas; j++) if (xEntrada[j] > 0) wEntrada[i][j] = Math.min(r.tetoEntradaE, wEntrada[i][j] + fator * xEntrada[j]);
        for (let m = 0; m < nExc; m++) if (m !== i) wEE[m][i] = Math.min(r.tetoEE, wEE[m][i] + fator * xExc[m]);
      }
      anelMenos[i][posicao] = uMenos[i];
      anelMais[i][posicao] = uMais[i];
      uMenos[i] += (dt / p.tauMenos) * (u - uMenos[i]);
      uMais[i] += (dt / p.tauMais) * (u - uMais[i]);
      media[i] += (dt / p.tauMedia) * (uMenos[i] - media[i]);
    }
    posicao = (posicao + 1) % comprimento;
    for (let j = 0; j < nEntradas; j++) {
      xEntrada[j] *= decaiX;
      if (aleatorio() < taxas[j]) novos.entradas.push(j);
    }
    for (let i = 0; i < nExc; i++) xExc[i] *= decaiX;
    chegando = novos;
  }
  return { wEE, wEntrada, taxas: Array.from(spikes, (s) => s / r.segundos) };
}

// As medidas da replicação: a mudança dos pesos E→E, a correlação recíproca, os pares fortes nos
// dois sentidos (forte = acima de metade do teto) e os campos receptivos (o centro de massa dos
// pesos de entrada de cada excitatório; "mesmo campo" = centros a menos de 25 entradas)
function medirRedeDeClopath({ wEE, wEntrada, taxas }, r = replicacaoDeClopath) {
  const nExc = wEE.length;
  const centros = wEntrada.map((w) => {
    let soma = 0;
    let pesado = 0;
    w.forEach((x, j) => {
      const acima = Math.max(0, x - media(Array.from(w)));
      soma += acima;
      pesado += acima * j;
    });
    return pesado / soma;
  });
  const ida = [];
  const volta = [];
  const forte = (x) => x > r.tetoEE / 2;
  let fortes = 0;
  let fortesNosDois = 0;
  const mesmoCampo = { w: [], pares: 0, fortesNosDois: 0 };
  const outroCampo = { w: [] };
  for (let i = 0; i < nExc; i++) {
    for (let j = 0; j < nExc; j++) {
      if (i === j) continue;
      if (forte(wEE[i][j])) fortes++;
      (Math.abs(centros[i] - centros[j]) < 25 ? mesmoCampo : outroCampo).w.push(wEE[i][j]);
      if (j <= i) continue;
      ida.push(wEE[i][j]);
      volta.push(wEE[j][i]);
      if (forte(wEE[i][j]) && forte(wEE[j][i])) fortesNosDois++;
      if (Math.abs(centros[i] - centros[j]) < 25) {
        mesmoCampo.pares++;
        if (forte(wEE[i][j]) && forte(wEE[j][i])) mesmoCampo.fortesNosDois++;
      }
    }
  }
  const pForte = fortes / (nExc * (nExc - 1));
  const pares = (nExc * (nExc - 1)) / 2;
  return {
    taxaE: media(taxas.slice(0, nExc)),
    taxaI: media(taxas.slice(nExc)),
    pesoEEMedio: media([...ida, ...volta]),
    fracaoForte: pForte,
    correlacaoReciproca: pearson(ida, volta),
    fortesNosDoisSobreEsperado: fortesNosDois / pares / pForte ** 2,
    fortesNosDois,
    campos: new Set(centros.map((c) => Math.round(c / 50))).size,
    pesoMesmoCampo: media(mesmoCampo.w),
    pesoOutroCampo: media(outroCampo.w),
    paresNoMesmoCampo: mesmoCampo.pares,
    fortesNosDoisNoMesmoCampo: mesmoCampo.fortesNosDois,
  };
}

// O código MATLAB dos autores (ModelDB 144566, RFdevelop.m e aEIF.m), passo a passo: um neurônio,
// 500 entradas, 10 padrões gaussianos circulares (σ = 10 entradas, 15 Hz no pico, 0,1 Hz de fundo)
// sorteados a cada 100 ms, dt = 1 ms, 100 s. A corrente é w·entrada·C·4 (cada unidade de peso dá
// 4 mV), os pesos começam em U(0,5; 2) e ficam em [0, 3]. A homeostase é a do código: θ é a média
// de (u − E_L)² em 1,2 s, e a LTD é multiplicada por θ/60. As amplitudes são 10× as do artigo,
// como no código ("para acelerar as simulações").
const campoReceptivoDeClopath = {
  nEntradas: 500,
  nPadroes: 10,
  epoca: 100, // ms
  epocas: 1000,
  sigma: 10,
  taxaMaxima: 0.015, // spikes por ms
  taxaMinima: 0.0001,
  tauHomeostase: 1200,
  alvoHomeostase: 60, // mV²
  aLTD: 10 * 0.00014,
  aLTP: 10 * 0.00008,
  tauMais: 7,
  tauR: 15,
  tauMenos: 10,
  eL: -70.6,
  wMax: 3,
};

// O aEIF.m: AdEx com corrente de pós-potencial e limiar adaptativo, passo de 1 ms, spike forçado a
// durar 2 ms com os valores que os autores integraram em resolução fina ("resolution trick")
function passoAEIF(s, corrente) {
  const C = 281;
  const gL = 30;
  const eL = -70.6;
  const vTRepouso = -50.4;
  if (s.contador === 2) {
    s.u = eL + 15 + 6.0984;
    s.w += 0.0805;
    s.wCauda = 400;
    s.contador = 0;
    s.vT = 20 + vTRepouso;
  }
  const du = (1 / C) * (-gL * (s.u - eL) + gL * 2 * Math.exp((s.u - s.vT) / 2) - s.w + s.wCauda + corrente);
  const dw = (1 / 144) * (4 * (s.u - eL) - s.w);
  s.u += du;
  s.w += dw;
  s.wCauda -= s.wCauda / 40;
  s.vT = vTRepouso / 50 + (1 - 1 / 50) * s.vT;
  let disparou = false;
  if (s.contador === 1) {
    s.contador = 2;
    s.u = 29.4 + 3.462;
    s.w -= dw;
  }
  if (s.u > 20 && s.contador === 0) {
    s.u = 29.4;
    s.contador = 1;
    disparou = true;
  }
  return disparou;
}

// RFdevelop.m. Devolve os pesos finais e, para cada padrão, a corrente média que ele daria.
function simularCampoReceptivoDeClopath(semente, c = campoReceptivoDeClopath) {
  semear(semente);
  const { nEntradas, nPadroes, eL } = c;
  const gauss = Float64Array.from({ length: nEntradas }, (_, i) => c.taxaMinima + c.taxaMaxima * Math.exp(-((i + 1 - nEntradas / 2) ** 2) / (2 * c.sigma ** 2)));
  const padroes = Array.from({ length: nPadroes }, (_, p) => {
    const inicio = (p * nEntradas) / nPadroes;
    return Float64Array.from({ length: nEntradas }, (_, i) => gauss[(inicio + i) % nEntradas]);
  });
  const w = Float64Array.from({ length: nEntradas }, () => aleatorio() * 1.5 + 0.5);
  const s = { u: eL, w: 0, wCauda: 0, vT: -50.4, contador: 0 };
  let uMp = eL;
  let uMd = eL;
  let theta = 0;
  let u1s = eL;
  let u1ss = eL;
  const r = new Float64Array(nEntradas);
  const entrada = new Uint8Array(nEntradas);
  let padrao = 0;
  let spikes = 0;
  const total = c.epoca * c.epocas;
  for (let t = 1; t < total; t++) {
    if (t % c.epoca === 0 || t === 1) padrao = Math.floor(nPadroes * aleatorio());
    let corrente = 0;
    for (let i = 0; i < nEntradas; i++) {
      entrada[i] = aleatorio() < padroes[padrao][i] ? 1 : 0;
      if (entrada[i]) corrente += w[i];
    }
    if (passoAEIF(s, corrente * 281 * 4)) spikes++;
    const u = s.u;
    const uy = u - eL > 25.3 ? u - eL - 25.3 : 0;
    uMp = u1ss / c.tauMais + (1 - 1 / c.tauMais) * uMp;
    uMd = u1ss / c.tauMenos + (1 - 1 / c.tauMenos) * uMd;
    const sinalMd = uMd - eL > 0 ? uMd - eL : 0;
    const sinalMp = uMp - eL > 0 ? uMp - eL : 0;
    theta = (1 - 1 / c.tauHomeostase) * theta + ((u1ss - eL) ** 2) / c.tauHomeostase;
    for (let i = 0; i < nEntradas; i++) {
      r[i] = (1 - 1 / c.tauR) * r[i] + entrada[i] / c.tauR;
      w[i] += c.aLTP * r[i] * sinalMp * uy - c.aLTD * entrada[i] * sinalMd * (theta / c.alvoHomeostase);
      w[i] = Math.min(c.wMax, Math.max(0, w[i]));
    }
    // o código faz u1s = u; u1ss = u1s, então os filtros leem o u do passo anterior (o comentário
    // dele fala em 2 ms, mas o que roda é 1 passo)
    u1s = u;
    u1ss = u1s;
  }
  const resposta = padroes.map((padraoP) => padraoP.reduce((soma, x, i) => soma + x * w[i], 0));
  return { w, resposta, taxa: spikes / (total / 1000) };
}

// O mesmo código com nNeuronios neurônios e conexões E→E entre todos, também com a regra (o cenário
// da figura 5, codificação por taxa). O artigo não está acessível aqui e o código dos autores não
// tem essa parte; as E→E seguem a proporção do exemplo do NEST (inicial 0,25 e teto 0,75, um quarto
// das entradas) e não há inibição. Cada spike pré chega ao pós no passo seguinte.
function simularRedeDeClopathDosAutores(semente, { nNeuronios = 10, segundos = 100, pesoEE = 0.25, tetoEE = 0.75 } = {}, c = campoReceptivoDeClopath) {
  semear(semente);
  const { nEntradas, nPadroes, eL } = c;
  const gauss = Float64Array.from({ length: nEntradas }, (_, i) => c.taxaMinima + c.taxaMaxima * Math.exp(-((i + 1 - nEntradas / 2) ** 2) / (2 * c.sigma ** 2)));
  const padroes = Array.from({ length: nPadroes }, (_, p) => Float64Array.from({ length: nEntradas }, (_, i) => gauss[((p * nEntradas) / nPadroes + i) % nEntradas]));
  const wEntrada = Array.from({ length: nNeuronios }, () => Float64Array.from({ length: nEntradas }, () => aleatorio() * 1.5 + 0.5));
  const wEE = Array.from({ length: nNeuronios }, (_, m) => Float64Array.from({ length: nNeuronios }, (_, i) => (m === i ? 0 : pesoEE))); // [pré][pós]
  const neuronios = Array.from({ length: nNeuronios }, () => ({ u: eL, w: 0, wCauda: 0, vT: -50.4, contador: 0 }));
  const uMp = new Float64Array(nNeuronios).fill(eL);
  const uMd = new Float64Array(nNeuronios).fill(eL);
  const theta = new Float64Array(nNeuronios);
  const uAnterior = new Float64Array(nNeuronios).fill(eL);
  const rEntrada = new Float64Array(nEntradas);
  const rEE = new Float64Array(nNeuronios);
  const entrada = new Uint8Array(nEntradas);
  let disparos = new Uint8Array(nNeuronios); // do passo anterior
  const spikes = new Float64Array(nNeuronios);
  let padrao = 0;
  const total = segundos * 1000;
  for (let t = 1; t < total; t++) {
    if (t % c.epoca === 0 || t === 1) padrao = Math.floor(nPadroes * aleatorio());
    for (let j = 0; j < nEntradas; j++) entrada[j] = aleatorio() < padroes[padrao][j] ? 1 : 0;
    for (let j = 0; j < nEntradas; j++) rEntrada[j] = (1 - 1 / c.tauR) * rEntrada[j] + entrada[j] / c.tauR;
    for (let m = 0; m < nNeuronios; m++) rEE[m] = (1 - 1 / c.tauR) * rEE[m] + disparos[m] / c.tauR;
    const novos = new Uint8Array(nNeuronios);
    for (let i = 0; i < nNeuronios; i++) {
      let corrente = 0;
      for (let j = 0; j < nEntradas; j++) if (entrada[j]) corrente += wEntrada[i][j];
      for (let m = 0; m < nNeuronios; m++) if (disparos[m]) corrente += wEE[m][i];
      if (passoAEIF(neuronios[i], corrente * 281 * 4)) {
        novos[i] = 1;
        spikes[i]++;
      }
      const u = neuronios[i].u;
      const uy = u - eL > 25.3 ? u - eL - 25.3 : 0;
      uMp[i] = uAnterior[i] / c.tauMais + (1 - 1 / c.tauMais) * uMp[i];
      uMd[i] = uAnterior[i] / c.tauMenos + (1 - 1 / c.tauMenos) * uMd[i];
      const sinalMd = uMd[i] - eL > 0 ? uMd[i] - eL : 0;
      const sinalMp = uMp[i] - eL > 0 ? uMp[i] - eL : 0;
      theta[i] = (1 - 1 / c.tauHomeostase) * theta[i] + ((uAnterior[i] - eL) ** 2) / c.tauHomeostase;
      const ltp = c.aLTP * sinalMp * uy;
      const ltd = c.aLTD * sinalMd * (theta[i] / c.alvoHomeostase);
      for (let j = 0; j < nEntradas; j++) {
        if (ltp === 0 && !entrada[j]) continue;
        wEntrada[i][j] = Math.min(c.wMax, Math.max(0, wEntrada[i][j] + ltp * rEntrada[j] - ltd * entrada[j]));
      }
      for (let m = 0; m < nNeuronios; m++) {
        if (m === i) continue;
        wEE[m][i] = Math.min(tetoEE, Math.max(0, wEE[m][i] + ltp * rEE[m] - ltd * disparos[m]));
      }
      uAnterior[i] = u;
    }
    disparos = novos;
  }
  const preferido = wEntrada.map((w) => {
    const resposta = padroes.map((p) => p.reduce((soma, x, j) => soma + x * w[j], 0));
    return resposta.indexOf(Math.max(...resposta));
  });
  return { wEE, preferido, taxas: Array.from(spikes, (s) => s / segundos), tetoEE };
}

// Reciprocidade da rede dos autores: no geral e entre neurônios com o mesmo padrão preferido
function medirRedeDosAutores({ wEE, preferido, taxas, tetoEE }) {
  const n = wEE.length;
  const forte = (x) => x > tetoEE / 2;
  const grupo = (mesmo) => {
    const ida = [];
    const volta = [];
    let fortesNosDois = 0;
    let fortesNoMaximoUm = 0;
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        if ((preferido[i] === preferido[j]) !== mesmo) continue;
        ida.push(wEE[i][j]);
        volta.push(wEE[j][i]);
        if (forte(wEE[i][j]) && forte(wEE[j][i])) fortesNosDois++;
        else if (forte(wEE[i][j]) || forte(wEE[j][i])) fortesNoMaximoUm++;
      }
    }
    return { pares: ida.length, pesoMedio: media([...ida, ...volta]), r: pearson(ida, volta), fortesNosDois, soUmForte: fortesNoMaximoUm };
  };
  return { taxa: media(taxas), campos: new Set(preferido).size, mesmo: grupo(true), diferente: grupo(false) };
}

// --segundos=<s> alonga a simulação e --amplitudes=<fator> multiplica A_LTP e A_LTD (o código MATLAB
// dos autores usa 10× as do artigo "para acelerar as simulações"; o exemplo do NEST usa 1/10)
function replicarRedeDeClopath() {
  const sementes = lerArgumento("sementes", "1,2,3,4,5").split(",").map(Number);
  console.log("\nCampo receptivo, o RFdevelop.m dos autores: 1 neurônio, 500 entradas, 10 padrões, 100 s");
  for (const semente of sementes) {
    const { w, resposta, taxa } = simularCampoReceptivoDeClopath(semente);
    const ordem = [...resposta].sort((a, b) => b - a);
    const melhor = resposta.indexOf(ordem[0]);
    // perfil dos pesos em 25 faixas de 20 entradas
    const perfil = Array.from({ length: 25 }, (_, k) => media(Array.from(w.slice(20 * k, 20 * k + 20))));
    const barras = perfil.map((x) => " ▁▂▃▄▅▆▇█"[Math.min(8, Math.round((8 * x) / campoReceptivoDeClopath.wMax))]).join("");
    linha(
      `semente ${semente}`,
      `${taxa.toFixed(1)} Hz · padrão preferido ${melhor} · resposta ao 1º / 2º / mediana dos padrões ${(ordem[0] / ordem[1]).toFixed(1)}× e ${(ordem[0] / ordem[5]).toFixed(1)}× · pesos [${barras}]`,
    );
  }
  const segundosDosAutores = Number(lerArgumento("segundosAutores", 200));
  console.log(`\nRede com o código dos autores: 10 neurônios, E→E com a regra, ${segundosDosAutores} s (sem inibição; E→E inicial 0,25, teto 0,75)`);
  const medidasDosAutores = sementes.map((semente) => medirRedeDosAutores(simularRedeDeClopathDosAutores(semente, { segundos: segundosDosAutores })));
  const resumo = (ler, casas = 2) => resumoEntreSementes(medidasDosAutores.map(ler), casas);
  linha("taxa (Hz) · campos receptivos distintos", `${resumo((m) => m.taxa, 1)} · ${resumo((m) => m.campos, 1)}`);
  for (const [rotulo, chave] of [["mesmo campo", "mesmo"], ["campos diferentes", "diferente"]]) {
    linha(`${rotulo}: pares · peso E→E médio`, `${resumo((m) => m[chave].pares, 1)} · ${resumo((m) => m[chave].pesoMedio, 3)}`);
    linha(`${rotulo}: r(w A→B, w B→A)`, resumo((m) => m[chave].r));
    linha(`${rotulo}: pares fortes nos dois sentidos · só num`, `${resumo((m) => m[chave].fortesNosDois, 1)} · ${resumo((m) => m[chave].soUmForte, 1)}`);
  }
  const fator = Number(lerArgumento("amplitudes", 1));
  const regra = { ...replicacaoDeClopath.regra, aLTP: fator * replicacaoDeClopath.regra.aLTP, aLTD: fator * replicacaoDeClopath.regra.aLTD };
  const r = { ...replicacaoDeClopath, segundos: Number(lerArgumento("segundos", replicacaoDeClopath.segundos)), regra };
  console.log(
    `\nRede de Clopath et al. (2010, fig. 5), como no exemplo do NEST: ${r.nExc} E + ${r.nInib} I, ${r.nEntradas} entradas, ` +
      `${r.segundos} s, amplitudes × ${fator}, sementes ${sementes.join(", ")}`,
  );
  const f = (x, c = 2) => (Number.isFinite(x) ? x.toFixed(c) : "—");
  for (const [nome, neuronio] of Object.entries(neuroniosDaReplicacao)) {
    const relogio = performance.now();
    const resultados = sementes.map((semente) => simularRedeDeClopath(semente, neuronio, r));
    const medidas = resultados.map((x) => medirRedeDeClopath(x, r));
    const resumo = (ler, casas = 2) => resumoEntreSementes(medidas.map(ler), casas);
    console.log(`\nneurônio: ${nome} (${((performance.now() - relogio) / 1000).toFixed(0)} s)`);
    linha("taxa E · taxa I (Hz)", `${resumo((m) => m.taxaE, 1)} · ${resumo((m) => m.taxaI, 1)}`);
    linha("peso E→E médio (início 0,25; teto 0,75)", resumo((m) => m.pesoEEMedio, 3));
    linha("fração das E→E fortes (> metade do teto)", resumo((m) => m.fracaoForte));
    linha("r(w A→B, w B→A), 45 pares", resumo((m) => m.correlacaoReciproca));
    linha("pares fortes nos dois sentidos / esperado", resumo((m) => m.fortesNosDoisSobreEsperado));
    linha("campos receptivos distintos (de 10 posições)", resumo((m) => m.campos, 1));
    linha("peso E→E: mesmo campo · campos diferentes", `${resumo((m) => m.pesoMesmoCampo, 3)} · ${resumo((m) => m.pesoOutroCampo, 3)}`);
    linha("pares no mesmo campo · fortes nos dois sentidos", `${resumo((m) => m.paresNoMesmoCampo, 1)} · ${resumo((m) => m.fortesNosDoisNoMesmoCampo, 1)}`);
    const { wEE } = resultados[0];
    console.log(`  pesos E→E da semente ${sementes[0]} (linha = de, coluna = para, × 100):`);
    for (const linhaDePesos of wEE) console.log(`    ${Array.from(linhaDePesos, (w) => f(100 * w, 0).padStart(4)).join("")}`);
  }
}

// Rode com: node index.js --conectoma [--fase=1|extra|lognormal|2|regras|neuronio-clopath|replicacao-clopath]
//           [--entrada=compartilhada|rajadas] [--condicoes=tripletos,pares,sem-plasticidade,...]
//           [--variante=teto|ruido-0.03|ruido-0.1] [--teto=4] [--bits=16|8] [--procedural] [--sementes=1,2,3] [--saida=<pasta>]
//      ou: node index.js --conectoma --analisar=<pasta>
// Cada condição simula as sementes × 900 s e grava um registro por semente em --saida (padrão:
// resultados/fase-<fase>-<entrada>[-<variante>]). Condições e sementes podem rodar em processos
// paralelos e ser analisadas juntas depois com --analisar. A fase lognormal usa os tripletos; a
// fase regras usa rajadas e fiação fixa.
function demonstracaoConectoma() {
  const pastaParaAnalisar = lerArgumento("analisar", null);
  if (pastaParaAnalisar) {
    const registros = lerRegistros(pastaParaAnalisar);
    console.log(`\nConectoma, análise de ${registros.length} registros em ${pastaParaAnalisar}`);
    analisarRegistros(registros);
    return;
  }
  const e = experimentoConectoma;
  const fase = lerArgumento("fase", "1");
  if (fase === "neuronio-clopath") {
    avaliarNeuronioDeClopath();
    return;
  }
  if (fase === "replicacao-clopath") {
    replicarRedeDeClopath();
    return;
  }
  const padraoDeCondicoes = {
    extra: "tripletos,pares",
    lognormal: "tripletos",
    regras: "tripletos,homeostase-congelada,sem-escalonamento,sem-istdp,tripletos-adex,clopath-adex",
  };
  const condicoes = lerArgumento("condicoes", padraoDeCondicoes[fase] ?? e.condicoes.join(",")).split(",").map((c) => c.replaceAll("-", " "));
  const nomeDaEntrada = lerArgumento("entrada", fase === "extra" || fase === "regras" ? "rajadas" : "compartilhada");
  const entrada = entradasDoConectoma[nomeDaEntrada];
  const nomeDaVariante = fase === "lognormal" ? lerArgumento("variante", "teto") : null;
  // --teto=<fator> sobe o teto E→E nas outras fases (a escala da LTP não muda); na lognormal ele vem da variante
  const fatorTeto = nomeDaVariante ? null : lerArgumento("teto", null);
  const variante = nomeDaVariante ? variantesDaLognormal[nomeDaVariante] : fatorTeto ? { fatorTeto: Number(fatorTeto) } : {};
  const sementes = lerArgumento("sementes", e.sementes.join(",")).split(",").map(Number);
  const bits = lerArgumento("bits", null);
  const procedural = process.argv.includes("--procedural");
  const sufixos = [nomeDaVariante, fatorTeto && `teto${fatorTeto}`, bits && `bits${bits}`, procedural && "procedural"];
  const pasta = lerArgumento("saida", join("resultados", ["fase", fase, nomeDaEntrada, ...sufixos].filter(Boolean).join("-")));
  const descricaoDaEntrada = entrada.rajadas
    ? `rajadas por grupo (${entrada.rajadas.taxaHz}/s, ${entrada.rajadas.duracao} ms, +${entrada.rajadas.entradaHz} Hz)`
    : `${100 * entrada.fracaoCorrelacionada}% de entrada compartilhada por grupo`;
  const estrutural = fase === "2" ? estruturalDoConectoma : null;
  const detalhes = [
    estrutural && `poda de ${100 * estrutural.fracao}% a cada ${estrutural.intervalo / 1000} s, novas com ${estrutural.pesoInicial} × a mediana`,
    nomeDaVariante && `teto ×${variante.fatorTeto}, ruído multiplicativo σ = ${variante.ruidoMultiplicativo}/√s`,
    fatorTeto && `teto E→E ×${fatorTeto}`,
    bits && `pesos em ${bits} bits`,
    procedural && "E→I e I→I procedurais",
  ].filter(Boolean);
  console.log(
    `\nConectoma, fase ${fase}: ${e.nNeuronios} neurônios, p = ${e.pConexao}, ${e.nGrupos} grupos, ${descricaoDaEntrada}, ` +
      `${e.segundos} s, sementes ${sementes.join(", ")}${detalhes.map((d) => `, ${d}`).join("")}; registros em ${pasta}`,
  );

  for (const condicao of condicoes) {
    const registros = sementes.map((semente) => {
      const arquivoDeSondas = join(pasta, `${nomeDaSemente(condicao, semente)}.sondas.csv`);
      const { registro } = rodarConectoma(condicao, semente, { ...entrada, ...variante, estrutural, arquivoDeSondas, ...(bits ? { bitsDosPesos: Number(bits) } : {}), conexoesProcedurais: procedural });
      const arquivo = salvarRegistro(registro, pasta);
      console.log(`  ${condicao}, semente ${semente}: ${registro.segundosDeRelogio} s → ${arquivo}`);
      return registro;
    });
    analisarRegistros(registros);
  }
}

// ============================================================================
// Modo --integrado: cada região do projeto é um módulo com a mesma interface
//   nome, nivel ("spikes" ou "populacao"), ligada, entradas ({ nome: valor }), saidas ({ nome: valor }),
//   padrao ({ saída: valor enquanto a região está desligada }), passo(dt, t, entradas) e sondas()
// O orquestrador liga saídas a entradas por vias com atraso de condução e anda de 1 em 1 ms. Uma
// região desligada não anda, e as suas saídas ficam no padrão (os níveis de vigília em que o córtex
// foi calibrado). Os moduladores do córtex vêm das regiões (prosencéfalo basal, locus coeruleus,
// VTA), não de botões; pistas e recompensas vêm do ambiente.
// Regiões: córtex (o Cerebro em spikes ou um Wilson-Cowan em população), hipotálamo, prosencéfalo
// basal, locus coeruleus, VTA e núcleos da base. O hipocampo espera, porque o replay de um padrão
// chega perto do "espaço de trabalho global" do CLAUDE.md; nos núcleos da base um canal vence, mas a
// escolha só abre a alça do próprio canal e o efetor, e o teste de entrada confere que ela não chega
// a nenhuma outra região.
// Linhas éticas: nenhuma região de dor, dano ou metacognição. A surpresa do locus coeruleus, a
// novidade do prosencéfalo basal e o erro da VTA são sobre o ambiente (pistas e recompensas), não
// sobre estados internos do sistema. Nas tarefas, errar só deixa de dar recompensa: não há punição.
// ============================================================================

// Canais do córtex: 4 grupos de 20 excitatórios; as pistas A, B e C do ambiente chegam aos canais 0, 1 e 2
const canaisDoCortex = [0, 1, 2, 3].map((k) => Array.from({ length: 20 }, (_, i) => 20 * k + i));
// No Pong: 6 grupos de 16 excitatórios (ver cerebroNoPong)
const canaisDoPong = Array.from({ length: 6 }, (_, k) => Array.from({ length: 16 }, (_, i) => 16 * k + i));
const nomesDosEstados = ["vigilia", "nrem", "rem"];

// Vias entre regiões: comprimento aproximado do axônio (mm, ordem de grandeza) e a fibra (diâmetro
// em µm, mielinizada ou não). O atraso é comprimento / velocidadeDeConducao (do 02) + 1 ms de
// sinapse. As fibras monoaminérgicas e colinérgicas são finas e quase todas sem mielina, por isso
// lentas. Perfis: "roedor" (rato, o padrão, coerente com os parâmetros e com o MICrONS) e "humano"
// (comprimentos ~8× maiores, para os experimentos de linguagem). O ambiente entra com uma latência
// sensorial fixa de cada perfil. As vias de canal saem para cada um dos nCanais do córtex, e as dos
// sensores do Pong para cada um dos nSensores.
const viasDoIntegrado = (nCanais = canaisDoCortex.length, nSensores = 2) => [
  { de: "hipotalamo.estado", para: "ambiente.estado", ms: { roedor: 1, humano: 1 } },
  { de: "hipotalamo.estado", para: "cortex.estado", ms: { roedor: 1, humano: 1 } }, // só para os testes de causa (noSono)
  { de: "hipotalamo.estado", para: "prosencefaloBasal.estado", mm: { roedor: 3, humano: 25 }, fibra: [0.5, false] },
  { de: "hipotalamo.estado", para: "locusCoeruleus.estado", mm: { roedor: 6, humano: 50 }, fibra: [0.5, false] },
  { de: "prosencefaloBasal.acetilcolina", para: "cortex.acetilcolina", mm: { roedor: 6, humano: 50 }, fibra: [0.5, false] },
  { de: "locusCoeruleus.noradrenalina", para: "cortex.noradrenalina", mm: { roedor: 15, humano: 120 }, fibra: [0.3, false] },
  { de: "locusCoeruleus.noradrenalinaFasica", para: "cortex.noradrenalinaFasica", mm: { roedor: 15, humano: 120 }, fibra: [0.3, false] },
  { de: "vta.dopamina", para: "cortex.dopamina", mm: { roedor: 8, humano: 65 }, fibra: [0.3, false] },
  { de: "ambiente.pista", para: "cortex.pista", sensorial: true },
  { de: "ambiente.pista", para: "prosencefaloBasal.pista", sensorial: true },
  { de: "ambiente.pista", para: "locusCoeruleus.pista", sensorial: true },
  { de: "ambiente.pista", para: "vta.pista", sensorial: true },
  { de: "ambiente.recompensa", para: "vta.recompensa", sensorial: true },
  // Núcleos da base: córtex → estriado, canal a canal; a dopamina com as pausas vem da VTA (SNc/VTA
  // → estriado); a saída de cada canal (GPi → tálamo → córtex, duas sinapses) volta só para o mesmo
  // canal do córtex e vai para o efetor com uma latência motora fixa
  ...Array.from({ length: nCanais }, (_, k) => [
    { de: `cortex.canal${k}`, para: `nucleosDaBase.canal${k}`, mm: { roedor: 4, humano: 30 }, fibra: [1, true] },
    { de: `nucleosDaBase.alca${k}`, para: `cortex.alca${k}`, mm: { roedor: 6, humano: 50 }, fibra: [2, true], sinapses: 2 },
    { de: `nucleosDaBase.alca${k}`, para: `ambiente.alca${k}`, motora: true },
  ]).flat(),
  { de: "vta.dopaminaComPausas", para: "nucleosDaBase.dopamina", mm: { roedor: 5, humano: 40 }, fibra: [0.3, false] },
  // Pong: os sensores chegam aos primeiros canais do córtex, e o começo de cada jogada à VTA
  ...Array.from({ length: nSensores }, (_, k) => ({ de: `ambiente.sensor${k}`, para: `cortex.sensor${k}`, sensorial: true, tarefa: "pong" })),
  { de: "ambiente.jogada", para: "vta.jogada", sensorial: true, tarefa: "pong" },
];
const latenciaSensorial = { roedor: 15, humano: 40 }; // ms
const latenciaMotora = { roedor: 20, humano: 50 }; // ms, da saída dos núcleos da base ao efetor (ordem de grandeza)

function atrasoDaVia(via, perfil) {
  if (via.sensorial) return latenciaSensorial[perfil];
  if (via.motora) return latenciaMotora[perfil];
  if (via.ms) return via.ms[perfil];
  const [diametroUm, mielinizado] = via.fibra;
  return via.mm[perfil] / velocidadeDeConducao(diametroUm, mielinizado) + (via.sinapses ?? 1); // mm / (m/s) = ms
}

// Roda fn com outro gerador no lugar de aleatorio (as regiões que sorteiam têm o seu, para os
// testes com e sem uma região verem o mesmo ambiente)
function comGerador(gerador, fn) {
  const anterior = aleatorio;
  aleatorio = gerador;
  try {
    return fn();
  } finally {
    aleatorio = anterior;
  }
}

// As vias com `tarefa` só existem nessa tarefa do ambiente
class CerebroIntegrado {
  constructor(regioes, { perfil = "roedor", tarefa = "pistas", nCanais = canaisDoCortex.length, nSensores = 2 } = {}) {
    this.regioes = regioes;
    this.t = 0;
    this.vias = viasDoIntegrado(nCanais, nSensores)
      .filter((via) => via.de.split(".")[0] in regioes && via.para.split(".")[0] in regioes && (via.tarefa ?? tarefa) === tarefa)
      .map((via) => {
        const [origem, saida] = via.de.split(".");
        const [destino, entrada] = via.para.split(".");
        const atraso = atrasoDaVia(via, perfil);
        const inicial = regioes[origem].padrao[saida];
        return { origem, saida, destino, entrada, atraso, anel: new Float64Array(Math.max(1, Math.round(atraso))).fill(inicial), posicao: 0 };
      });
  }

  // As vias primeiro: cada uma guarda a saída de agora e entrega a de `atraso` ms atrás; depois
  // cada região ligada anda 1 ms
  passo(dt = 1) {
    for (const via of this.vias) {
      const origem = this.regioes[via.origem];
      const valor = origem.ligada ? origem.saidas[via.saida] : origem.padrao[via.saida];
      this.regioes[via.destino].entradas[via.entrada] = via.anel[via.posicao];
      via.anel[via.posicao] = valor;
      via.posicao = (via.posicao + 1) % via.anel.length;
    }
    this.t += dt;
    for (const regiao of Object.values(this.regioes)) if (regiao.ligada) regiao.passo(dt, this.t, regiao.entradas);
  }
}

// --- O ambiente ---------------------------------------------------------------------------------

// Acordado, ensaios separados por 3 a 6 s ao acaso (com intervalo fixo, o fim de um ensaio prevê
// o começo do próximo, e a pista A deixa de ser surpresa para a VTA): a pista A (200 ms); 500 ms
// depois, B (80% das vezes) ou C (a rara, a surpresa), também por 200 ms; 1,2 s depois de B, a
// recompensa (90%; as outras são omissões). Dormindo, nada. Gerador próprio. Guarda um diário dos
// eventos para os testes.
// Tarefa "escolha" (com os núcleos da base): a mesma sequência de pistas, mas a recompensa só vem,
// no mesmo instante, se a resposta depois de B foi a ação acaoCerta (o canal 3, que não tem pista).
// A resposta é o primeiro canal que fica 100 ms seguidos com a alça acima de 0,5 entre o começo de
// B (ou de C) e 1 s depois (se dois completam juntos, o mais aberto); se nenhum fica, a resposta é
// −1. O sorteio dos 90% continua sendo feito, para a sequência de pistas ser a mesma das duas
// tarefas, mas não vale.
function criarAmbiente(semente, { tarefa = "pistas", acaoCerta = 3 } = {}) {
  const sortear = mulberry32(semente * 7919 + 13);
  const nCanais = canaisDoCortex.length;
  const ambiente = {
    nome: "ambiente",
    nivel: "populacao",
    ligada: true,
    entradas: { estado: 0, ...Object.fromEntries(canaisDoCortex.map((_, k) => [`alca${k}`, 0])) },
    saidas: { pista: -1, recompensa: 0 },
    padrao: { pista: -1, recompensa: 0 },
    diario: [], // { t, tipo: "A" | "B" | "C" | "recompensa" | "omissao" | "resposta" }
    eventos: [],
    proximoEnsaio: 1000,
    passo(dt, t, entradas) {
      const { estado } = entradas;
      if (t >= this.proximoEnsaio) {
        if (estado === 0) {
          const segunda = sortear() < 0.8 ? 1 : 2;
          this.eventos.push({ de: t, ate: t + 200, pista: 0 }, { de: t + 500, ate: t + 700, pista: segunda });
          const resposta = tarefa === "escolha" ? { janela: [t + 500, t + 1500], pista: segunda, desde: new Array(nCanais).fill(null), acao: null } : null;
          if (resposta) this.eventos.push(resposta);
          if (segunda === 1) {
            const sorteio = sortear() < 0.9;
            this.eventos.push({ recompensa: t + 1700, entregue: resposta ? null : sorteio, resposta });
          }
        }
        this.proximoEnsaio = t + 3000 + 3000 * sortear();
      }
      this.saidas.pista = -1;
      this.saidas.recompensa = 0;
      for (const evento of this.eventos) {
        if (evento.janela) {
          if (evento.acao !== null || t < evento.janela[0]) continue;
          let melhor = -1;
          for (let k = 0; k < nCanais; k++) {
            const alca = entradas[`alca${k}`];
            if (alca <= 0.5) evento.desde[k] = null;
            else if (evento.desde[k] === null) evento.desde[k] = t;
            else if (t - evento.desde[k] >= 100 && (melhor < 0 || alca > entradas[`alca${melhor}`])) melhor = k;
          }
          if (melhor >= 0) evento.acao = melhor;
          else if (t >= evento.janela[1] - 1) evento.acao = -1;
          if (evento.acao !== null) this.diario.push({ t, tipo: "resposta", pista: evento.pista, acao: evento.acao });
        } else if (evento.recompensa !== undefined) {
          if (Math.round(evento.recompensa) === Math.round(t)) {
            const entregue = evento.resposta ? evento.resposta.acao === acaoCerta : evento.entregue;
            this.saidas.recompensa = entregue ? 1 : 0;
            this.diario.push({ t, tipo: entregue ? "recompensa" : "omissao" });
          }
        } else if (t >= evento.de && t < evento.ate) {
          if (Math.round(t) === Math.round(evento.de)) this.diario.push({ t, tipo: "ABC"[evento.pista] });
          this.saidas.pista = evento.pista;
        }
      }
      this.eventos = this.eventos.filter((evento) => (evento.recompensa ?? evento.ate ?? evento.janela[1]) > t);
    },
    sondas() {
      return { pista: this.saidas.pista, recompensa: this.saidas.recompensa };
    },
  };
  return ambiente;
}

// Pong: o do Manus (manus/index.js, servirPongContraV1), espelhado para o cérebro ficar à esquerda,
// contra o algoritmo de lá, o v1. É a única versão do jogo.
// Campo de 0 a 1, paredes em 0,025 e 0,975; raquetes nas linhas x = 0,075 (cérebro) e 0,925 (v1),
// com meia altura 0,2 e o centro entre 0,09 e 0,91. O saque sai do meio a 0,78/s na horizontal e
// até ±0,38/s na vertical, para quem fez o último ponto; a cada rebatida |vx| sobe 1% e vy ganha
// 0,35 × (ponto de contato − centro). Ponto quando a bola passa de −0,03 ou de 1,03. No saque, a
// raquete do cérebro volta ao meio e a do v1 fica onde está (como lá). Lá o jogo anda em quadros de
// 1000/60 ms; aqui, de 1 ms.
//   v1: mira y + (vy/|vx|)·d·0,55, com d a distância da bola até a linha do cérebro (lá, a do
//       agente), e anda clip(alvo − v1, ±1)·3,4 por s.
//   cérebro: a velocidade vai para (alça de subir − alça de descer)·3,4 por s com τ = 70 ms (como
//       a do agente de lá). Recompensa só na rebatida, sem punição (lá: −0,5 por bola perdida).
// jogada vale 1 nos primeiros 100 ms de cada bola que vem para o cérebro (a pista J da VTA).
// Sono: quando o hipotálamo passa 1 s seguido dormindo (a mesma regra das transições de
// rodarIntegrado), o jogo para: a bola fica onde está, os sensores vão a 0 e nada é recompensado, e o
// diário marca "dormiu". Quando ele passa 1 s acordado, o diário marca "acordou" e sai um saque para
// o cérebro. Quem lê o estado é o jogo, que espera o jogador acordar, e não o cérebro. Com o
// hipotálamo desligado, a entrada fica no padrão (acordado) e o jogo nunca para.
// Gerador próprio. O diário guarda cada jogada e o resultado.
const fisicaDoPong = {
  paredes: [0.025, 0.975], linhas: [0.075, 0.925], meiaRaquete: 0.2, centro: [0.09, 0.91],
  vxDoSaque: 0.78, vyDoSaque: 0.38, aceleracao: 1.01, efeito: 0.35, fora: 0.03,
  velocidade: 3.4, tauDaRaquete: 70, previsaoDoV1: 0.55,
};

// Os sentidos e o motor do cérebro no Pong: 6 canais de 16 excitatórios (canaisDoPong). Os sensores
// chegam aos canais 0 a 3 do córtex, e só eles chegam ao estriado; as ações são os canais 4 (subir) e
// 5 (descer).
//   0 e 1: o quanto a bola está acima e abaixo do centro da raquete, de 0 a 1 (1 a partir de
//          alcanceDoSensor);
//   2 e 3: bola subindo e bola descendo, só enquanto ela vem para o cérebro, na proporção de |vy|
//          (até vyDeReferencia) e da distância que falta (1 na linha do v1, 0 na do cérebro).
// A direção e a distância são o que o agente de Q-learning do Manus recebia no estado; aqui elas
// chegam ao córtex como entrada sensorial, e o que fazer com elas o estriado aprende. Só com 0 e 1,
// o cérebro só perseguia a bola. orcamento: ver criarNucleosDaBase.
const cerebroNoPong = {
  canais: canaisDoPong,
  entradas: [0, 1, 2, 3],
  acoes: [4, 5],
  nomes: ["bola acima", "bola abaixo", "bola subindo", "bola descendo", "subir", "descer"],
  orcamento: "por entrada",
  alcanceDoSensor: 0.25,
  vyDeReferencia: 1, // por s, o |vy| que faz os sensores de direção chegarem a 1
};

// Os sensores do Pong: relativa = altura da bola − centro da raquete; vindo: a bola vem para o
// cérebro; distancia: de 0 (na linha do cérebro) a 1 (na do v1); vy por s
function sentirOPong(saidas, { relativa, vindo, distancia, vy }) {
  const { alcanceDoSensor, vyDeReferencia } = cerebroNoPong;
  saidas.sensor0 = Math.min(1, Math.max(0, relativa / alcanceDoSensor));
  saidas.sensor1 = Math.min(1, Math.max(0, -relativa / alcanceDoSensor));
  const movimento = vindo ? Math.min(1, Math.abs(vy) / vyDeReferencia) * Math.min(1, Math.max(0, distancia)) : 0;
  saidas.sensor2 = vy > 0 ? movimento : 0;
  saidas.sensor3 = vy < 0 ? movimento : 0;
}

function criarPong(semente, { f = fisicaDoPong } = {}) {
  const sortear = mulberry32(semente * 7919 + 29);
  const [sobeNa, desceNa] = cerebroNoPong.acoes.map((k) => `alca${k}`);
  const sensores = Object.fromEntries(cerebroNoPong.entradas.map((k) => [`sensor${k}`, 0]));
  const limitar = (x, a, b) => Math.max(a, Math.min(b, x));
  const bola = { x: 0.5, y: 0.5, vx: -f.vxDoSaque, vy: 0.28 }; // por s; o primeiro saque vai para o cérebro
  let raquete = 0.5;
  let velocidade = 0;
  let v1 = 0.5;
  let inicioDaJogada = 0;
  let dormindo = false;
  let outroEstadoDesde = null; // desde quando o hipotálamo diz o contrário de `dormindo`
  const sacar = (t, paraOCerebro) => {
    Object.assign(bola, { x: 0.5, y: 0.5, vx: (paraOCerebro ? -1 : 1) * f.vxDoSaque, vy: (sortear() * 2 - 1) * f.vyDoSaque });
    raquete = 0.5;
    if (paraOCerebro) comecarJogada(t);
  };
  const comecarJogada = (t) => {
    inicioDaJogada = t;
    pong.diario.push({ t, tipo: "jogada", y: bola.y });
  };
  const pong = {
    nome: "ambiente",
    nivel: "populacao",
    ligada: true,
    entradas: { estado: 0, ...Object.fromEntries(cerebroNoPong.canais.map((_, k) => [`alca${k}`, 0])) },
    saidas: { pista: -1, recompensa: 0, jogada: 0, ...sensores },
    padrao: { pista: -1, recompensa: 0, jogada: 0, ...sensores },
    diario: [], // { t, tipo: "jogada" | "rebatida" | "erro" | "ponto" (o v1 errou) | "dormiu" | "acordou" }
    placar: { cerebro: 0, algoritmo: 0 },
    passo(dt, t, entradas) {
      this.saidas.recompensa = 0;
      // o sono do jogador
      const querDormir = entradas.estado !== 0;
      if (querDormir === dormindo) outroEstadoDesde = null;
      else {
        outroEstadoDesde ??= t;
        if (t - outroEstadoDesde >= 1000) {
          dormindo = querDormir;
          outroEstadoDesde = null;
          this.diario.push({ t, tipo: dormindo ? "dormiu" : "acordou" });
          if (dormindo) velocidade = 0;
          else sacar(t, true);
        }
      }
      if (dormindo) {
        this.saidas.jogada = 0;
        for (const chave in sensores) this.saidas[chave] = 0;
        return;
      }
      const s = dt / 1000;
      // o v1
      const d = Math.max(0.02, bola.x);
      const alvo = limitar(bola.y + (bola.vy / Math.abs(bola.vx)) * d * f.previsaoDoV1, f.centro[0], f.centro[1]);
      v1 = limitar(v1 + limitar(alvo - v1, -1, 1) * f.velocidade * s, f.centro[0], f.centro[1]);
      // o cérebro
      const comando = Math.max(-1, Math.min(1, entradas[sobeNa] - entradas[desceNa]));
      velocidade += (comando * f.velocidade - velocidade) * (1 - Math.exp(-dt / f.tauDaRaquete));
      raquete = limitar(raquete + velocidade * s, f.centro[0], f.centro[1]);
      if (raquete === f.centro[0] || raquete === f.centro[1]) velocidade = 0;
      // a bola
      bola.x += bola.vx * s;
      bola.y += bola.vy * s;
      if (bola.y < f.paredes[0] || bola.y > f.paredes[1]) {
        bola.y = limitar(bola.y, f.paredes[0], f.paredes[1]);
        bola.vy *= -1;
      }
      if (bola.vx < 0 && bola.x < f.linhas[0] && Math.abs(bola.y - raquete) < f.meiaRaquete) {
        bola.x = f.linhas[0];
        bola.vx = Math.abs(bola.vx) * f.aceleracao;
        bola.vy += (bola.y - raquete) * f.efeito;
        this.saidas.recompensa = 1;
        this.diario.push({ t, tipo: "rebatida" });
      }
      if (bola.vx > 0 && bola.x > f.linhas[1] && Math.abs(bola.y - v1) < f.meiaRaquete) {
        bola.x = f.linhas[1];
        bola.vx = -Math.abs(bola.vx) * f.aceleracao;
        bola.vy += (bola.y - v1) * f.efeito;
        comecarJogada(t);
      }
      if (bola.x < -f.fora) {
        this.diario.push({ t, tipo: "erro" });
        this.placar.algoritmo++;
        sacar(t, false);
      } else if (bola.x > 1 + f.fora) {
        this.diario.push({ t, tipo: "ponto" });
        this.placar.cerebro++;
        sacar(t, true);
      }
      this.saidas.jogada = t - inicioDaJogada < 100 ? 1 : 0;
      const distancia = (bola.x - f.linhas[0]) / (f.linhas[1] - f.linhas[0]);
      sentirOPong(this.saidas, { relativa: bola.y - raquete, vindo: bola.vx < 0, distancia, vy: bola.vy });
    },
    // para a visualização: as posições, a velocidade da bola e se o jogo espera o jogador acordar
    posicoes() {
      const travessia = ((f.linhas[1] - f.linhas[0]) / Math.abs(bola.vx)) * 1000;
      return { bolaX: bola.x, bolaY: bola.y, raquete, adversario: v1, meiaRaquete: f.meiaRaquete, travessia, linhas: f.linhas, dormindo };
    },
    sondas() {
      return { bolaX: bola.x, bolaY: bola.y, raquete, recompensa: this.saidas.recompensa };
    },
  };
  pong.diario.push({ t: 0, tipo: "jogada", y: bola.y });
  return pong;
}

// O agente de Q-learning do Manus (servirPongContraV1), para comparar: no lado direito do jogo de
// lá, contra o v1, quadros de 1000/60 ms. O estado é (faixa de x da bola em 6, erro de altura em 7,
// sinal de vy, sinal de vx); as ações são −1, 0 e 1; ε começa em 0,12 e cai 0,03% por quadro até
// 0,02; α = 0,12 e γ = 0,92. As recompensas são as de lá: +1 na rebatida, −0,5 quando a bola passa
// por ele, −0,0004 por quadro andando e −1 quando ele faz ponto (parece um sinal trocado; com
// corrigirSinal, +1). Lá, o córtex somava 0,002 × a taxa de cada canal aos valores de Q, um
// desempate de ~1% que fica de fora. Devolve os diários de pontos.
function jogarComoOAgenteDoManus(semente, segundos, { corrigirSinal = false, f = fisicaDoPong } = {}) {
  const sortear = mulberry32(semente * 7919 + 31);
  const limitar = (x, a, b) => Math.max(a, Math.min(b, x));
  const jogo = { bola: { x: 0.5, y: 0.5, vx: 0.78, vy: 0.28 }, v1: 0.5, agente: 0.5, velocidadeAgente: 0, idadeAcao: 0, acao: 0, recompensa: 0 };
  const q = new Map();
  let epsilon = 0.12;
  const alfa = 0.12;
  const gamma = 0.92;
  const estado = () => {
    const zona = Math.max(0, Math.min(5, Math.floor(jogo.bola.x * 6)));
    const erro = Math.max(-3, Math.min(3, Math.round((jogo.bola.y - jogo.agente) * 6)));
    return `${zona}:${erro}:${jogo.bola.vy < 0 ? 0 : 1}:${jogo.bola.vx < 0 ? 0 : 1}`;
  };
  const valores = (s) => {
    if (!q.has(s)) q.set(s, [0, 0, 0]);
    return q.get(s);
  };
  const reiniciar = (sentido) => {
    jogo.bola = { x: 0.5, y: 0.5, vx: 0.78 * sentido, vy: (sortear() * 2 - 1) * 0.38 };
    jogo.agente = 0.5;
  };
  const eventos = [];
  const dt = 1000 / 60;
  let t = 0;
  const passoDoAmbiente = () => {
    const distancia = Math.max(0.02, 1 - jogo.bola.x);
    const alvoV1 = limitar(jogo.bola.y + (jogo.bola.vy / Math.abs(jogo.bola.vx)) * distancia * f.previsaoDoV1, 0.09, 0.91);
    jogo.v1 = limitar(jogo.v1 + limitar(alvoV1 - jogo.v1, -1, 1) * 0.0034 * dt, 0.09, 0.91);
    jogo.velocidadeAgente += (jogo.acao * 3.4 - jogo.velocidadeAgente) * (1 - Math.exp(-dt / 70));
    jogo.agente = limitar(jogo.agente + (jogo.velocidadeAgente * dt) / 1000, 0.09, 0.91);
    if (jogo.agente === 0.09 || jogo.agente === 0.91) jogo.velocidadeAgente = 0;
    jogo.recompensa = -0.0004 * Math.abs(jogo.acao);
    jogo.bola.x += (jogo.bola.vx * dt) / 1000;
    jogo.bola.y += (jogo.bola.vy * dt) / 1000;
    if (jogo.bola.y < 0.025 || jogo.bola.y > 0.975) {
      jogo.bola.y = limitar(jogo.bola.y, 0.025, 0.975);
      jogo.bola.vy *= -1;
    }
    if (jogo.bola.vx < 0 && jogo.bola.x < 0.075 && Math.abs(jogo.bola.y - jogo.v1) < 0.2) {
      jogo.bola.x = 0.075;
      jogo.bola.vx = Math.abs(jogo.bola.vx) * 1.01;
      jogo.bola.vy += (jogo.bola.y - jogo.v1) * 0.35;
    }
    if (jogo.bola.vx > 0 && jogo.bola.x > 0.925 && Math.abs(jogo.bola.y - jogo.agente) < 0.2) {
      jogo.bola.x = 0.925;
      jogo.bola.vx = -Math.abs(jogo.bola.vx) * 1.01;
      jogo.bola.vy += (jogo.bola.y - jogo.agente) * 0.35;
      jogo.recompensa = 1;
      eventos.push({ t, tipo: "rebatida" });
    }
    if (jogo.bola.x < -0.03) {
      jogo.recompensa = corrigirSinal ? 1 : -1;
      eventos.push({ t, tipo: "ponto" });
      reiniciar(1);
    }
    if (jogo.bola.x > 1.03) {
      jogo.recompensa = -0.5;
      eventos.push({ t, tipo: "erro" });
      reiniciar(-1);
    }
  };
  let anterior = estado();
  for (let quadro = 0; quadro < (segundos * 1000) / dt; quadro++) {
    t += dt;
    const acaoAnterior = jogo.acao;
    passoDoAmbiente();
    const atual = estado();
    const v = valores(anterior);
    v[acaoAnterior + 1] += alfa * (jogo.recompensa + gamma * Math.max(...valores(atual)) - v[acaoAnterior + 1]);
    anterior = atual;
    const pontuacoes = valores(atual);
    const candidato = sortear() < epsilon ? Math.floor(sortear() * 3) - 1 : pontuacoes.indexOf(Math.max(...pontuacoes)) - 1;
    const melhor = pontuacoes.indexOf(Math.max(...pontuacoes)) - 1;
    const novo = candidato === jogo.acao ? candidato : melhor;
    jogo.idadeAcao++;
    if (jogo.idadeAcao >= 6 || jogo.recompensa !== 0) {
      const atualScore = pontuacoes[jogo.acao + 1] ?? -Infinity;
      const novoScore = pontuacoes[novo + 1] ?? -Infinity;
      if (novo === jogo.acao || novoScore > atualScore + 0.06 || jogo.recompensa !== 0) {
        jogo.acao = novo;
        jogo.idadeAcao = 0;
      }
    }
    epsilon = Math.max(0.02, epsilon * 0.9997);
  }
  return eventos;
}

// --- Córtex ------------------------------------------------------------------------------------------

// Wilson-Cowan do córtex (nível de população): uma população E por canal, uma para o resto dos
// excitatórios e uma I comum, com taxas em Hz:
//   τ_E dE_k/dt = −E_k + S(g_rec·c_EE·E_k + c_cruz·Ē − c_EI·I + g_ext·(h_E + pista_k))
//   τ_I dI/dt = −I + S_I(c_IE·Ē − c_II·I + h_I),  S(x) = r_max/(1 + e^(−(x − θ)/(σ·a)))
// g_ext, g_rec e a (adaptação) são os efeitos dos moduladores do Cerebro (efeitosDosModuladores).
// hE e a força da pista foram ajustados (busca em grade, sozinho e acordado) para ~5 Hz de fundo e
// ~30 Hz no fim de uma pista de 200 ms, como o córtex em spikes; no modo integrado, a média durante
// a pista fica em ~15 Hz contra ~30 Hz em spikes. O ajuste fino ao córtex em spikes é o item 6e.
const wilsonCowanDoCortex = {
  tauE: 10, tauI: 5, rMax: 100, theta: 30, sigma: 5, thetaI: 30, sigmaI: 5,
  cEE: 0.5, cCruz: 0.2, cEI: 0.6, cIE: 1.2, cII: 0.4, hE: 21.5, hI: 22, pista: 2,
  // A entrada do tálamo num canal com a alça toda aberta (os sensores do Pong usam a força da pista).
  // Fica em 0 porque este Wilson-Cowan tem um segundo estado estável, com o canal a ~98 Hz, e no fim
  // de uma pista ele está perto da fronteira: com a alça a 0,5 ou mesmo 0,1 o canal da pista ia para
  // lá na tarefa de escolha e não voltava. Até o ajuste do item 6e, a alça só chega ao córtex em
  // spikes, e o Pong (entrada longa nos sensores) pede o córtex em spikes.
  alca: 0,
};

// Entrada Poisson extra por neurônio do canal no córtex em spikes (Hz): a pista, um sensor do Pong
// em 1 e a alça dos núcleos da base toda aberta (tálamo, ~4 Hz a mais no canal). A da alça é bem
// menor que a da pista para a alça sozinha não manter o canal escolhido: com 1000 Hz (~9 Hz a mais),
// depois do aprendizado o peso do canal sobre a própria ação chegava ao teto, a alça se mantinha
// sozinha, a raquete passava da bola, e o Pong aprendia o mapa ao contrário em 2 de 3 sementes.
const entradaDosCanais = { pista: 4000, sensor: 4000, alca: 400 };

// noSono (para os testes de causa): o que desligar enquanto o hipotálamo dorme, entre
// "escalonamento", "stdp", "istdp" e "recorrencia" (o aumento da recorrência E→E sem ACh).
// canais: os grupos de excitatórios que formam os canais (canaisDoCortex, ou canaisDoPong no Pong)
function criarCortex({ nivel = "spikes", noSono = [], canais = canaisDoCortex } = {}) {
  const nCanais = canais.length;
  const porCanal = (prefixo, valor) => Object.fromEntries(canais.map((_, k) => [`${prefixo}${k}`, valor]));
  const chavesDoSensor = canais.map((_, k) => `sensor${k}`);
  const chavesDaAlca = canais.map((_, k) => `alca${k}`);
  const cortex = {
    nome: "córtex",
    nivel,
    ligada: true,
    entradas: { acetilcolina: 1, noradrenalina: 0.5, noradrenalinaFasica: 0, dopamina: 0, pista: -1, estado: 0, ...porCanal("alca", 0), ...porCanal("sensor", 0) },
    saidas: { taxaE: 0, taxaI: 0, ...porCanal("canal", 0) },
    padrao: porCanal("canal", 0),
  };
  const suavizar = (k, contagem, tamanho, dt) => {
    const tau = 100;
    const instantanea = contagem / tamanho / (dt / 1000);
    cortex.saidas[k] += (dt / tau) * (instantanea - cortex.saidas[k]);
  };
  if (nivel === "spikes") {
    const cerebro = new Cerebro({ moduladoresDeFora: true, registrarTraco: false });
    const canalDe = new Int32Array(cerebro.n).fill(-1);
    canais.forEach((canal, k) => canal.forEach((i) => (canalDe[i] = k)));
    cortex.cerebro = cerebro;
    let dormindo = false;
    cortex.passo = (dt, t, e) => {
      if ((e.estado !== 0) !== dormindo && noSono.length) {
        dormindo = e.estado !== 0;
        for (const chave of ["escalonamento", "stdp", "istdp"]) if (noSono.includes(chave)) cerebro.config[chave] = !dormindo;
        if (noSono.includes("recorrencia")) cerebro.efeitosDosModuladores = dormindo ? { ...efeitosDosModuladores, recorrenciaSemACh: 0 } : efeitosDosModuladores;
      }
      cerebro.moduladoresRecebidos = {
        acetilcolina: e.acetilcolina,
        noradrenalina: e.noradrenalina,
        noradrenalinaFasica: e.noradrenalinaFasica,
        dopaminaFasica: e.dopamina,
      };
      if (e.pista >= 0) cerebro.estimular(canais[e.pista], dt, entradaDosCanais.pista);
      for (let k = 0; k < nCanais; k++) {
        if (e[chavesDoSensor[k]] > 0) cerebro.estimular(canais[k], dt, entradaDosCanais.sensor * e[chavesDoSensor[k]]);
        if (e[chavesDaAlca[k]] > 0) cerebro.estimular(canais[k], dt, entradaDosCanais.alca * e[chavesDaAlca[k]]);
      }
      cerebro.simular(dt);
      const { spikes } = cerebro.esvaziarRegistro();
      if (cortex.spikesRecentes) for (const valor of spikes) cortex.spikesRecentes.push(valor); // para a visualização do Pong
      const contagem = new Float64Array(nCanais + 2); // canais, E e I
      for (let q = 0; q < spikes.length; q += 2) {
        const i = spikes[q];
        if (i >= cerebro.config.nExc) contagem[nCanais + 1]++;
        else {
          contagem[nCanais]++;
          if (canalDe[i] >= 0) contagem[canalDe[i]]++;
        }
      }
      canais.forEach((canal, k) => suavizar(`canal${k}`, contagem[k], canal.length, dt));
      suavizar("taxaE", contagem[nCanais], cerebro.config.nExc, dt);
      suavizar("taxaI", contagem[nCanais + 1], cerebro.config.nInib, dt);
    };
    // peso E→E médio dentro de cada canal e fora deles, e a fração no teto (lido só nas sondas)
    cortex.pesos = () => {
      const { wMax } = cerebro.pesos.EE;
      const dentro = [];
      const fora = [];
      const inibitorias = [];
      let noTeto = 0;
      let total = 0;
      cerebro.paraCadaSinapse(({ pre, pos, tipo, w }) => {
        if (tipo === "IE") inibitorias.push(w);
        if (tipo !== "EE") return;
        total++;
        if (w >= 0.99 * wMax) noTeto++;
        (canalDe[pre] >= 0 && canalDe[pre] === canalDe[pos] ? dentro : fora).push(w);
      });
      return { dentro: media(dentro), fora: media(fora), noTeto: noTeto / total, ie: media(inibitorias) };
    };
    // O que o córtex aprendeu, para salvar em disco: os pesos das sinapses guardadas (E→E pela STDP e
    // escalonamento, I→E pelo iSTDP) e a taxa média de cada neurônio (a referência do escalonamento).
    // carregar põe isso num córtex criado com a mesma semente (a mesma fiação) e zera a elegibilidade.
    cortex.aprendido = () => ({ nSinapses: cerebro.nSinapses, pesos: Array.from(cerebro.sinapse.w), taxas: cerebro.neuronios.map((n) => n.taxa) });
    cortex.carregar = ({ nSinapses, pesos, taxas }) => {
      if (nSinapses !== cerebro.nSinapses) throw new Error(`o córtex salvo tem ${nSinapses} sinapses e este tem ${cerebro.nSinapses}: outra semente ou outra versão`);
      cerebro.sinapse.w.set(pesos);
      cerebro.sinapse.elegibilidade.fill(0);
      taxas.forEach((taxa, i) => (cerebro.neuronios[i].taxa = taxa));
    };
  } else {
    const p = wilsonCowanDoCortex;
    const emCanais = somar(canais.map((canal) => canal.length));
    const E = new Float64Array(nCanais + 1).fill(5); // canais e o resto
    let I = 10;
    const S = (x, theta, sigma, a) => p.rMax / (1 + Math.exp(-(x - theta) / (sigma * a)));
    const efeitos = {};
    cortex.passo = (dt, t, e) => {
      const { ganhoExterno, recorrencia, adaptacao } = calcularEfeitos(
        { acetilcolina: e.acetilcolina, noradrenalina: e.noradrenalina, noradrenalinaFasica: e.noradrenalinaFasica, dopaminaFasica: e.dopamina },
        efeitos,
      );
      // os canais têm emCanais dos 100 excitatórios do Cerebro (80 com os 4 canais) e o resto fora deles
      const mediaE = ((emCanais / 100) * (E.reduce((s, x) => s + x, 0) - E[nCanais])) / nCanais + ((100 - emCanais) / 100) * E[nCanais];
      const novos = E.map((Ek, k) => {
        const pista = (k === e.pista ? p.pista : 0) + (k < nCanais ? p.pista * e[chavesDoSensor[k]] + p.alca * e[chavesDaAlca[k]] : 0);
        const x = recorrencia * p.cEE * Ek + p.cCruz * mediaE - p.cEI * I + ganhoExterno * (p.hE + pista);
        return Ek + (dt / p.tauE) * (-Ek + S(x, p.theta, p.sigma, adaptacao));
      });
      I += (dt / p.tauI) * (-I + S(p.cIE * mediaE - p.cII * I + p.hI, p.thetaI, p.sigmaI, 1));
      E.set(novos);
      canais.forEach((_, k) => (cortex.saidas[`canal${k}`] = E[k]));
      cortex.saidas.taxaE = mediaE;
      cortex.saidas.taxaI = I;
    };
    cortex.pesos = () => ({ dentro: NaN, fora: NaN, noTeto: NaN });
    cortex.aprendido = () => ({}); // o Wilson-Cowan não aprende
    cortex.carregar = () => {};
  }
  cortex.sondas = () => ({ ...cortex.saidas });
  return cortex;
}

// --- Hipotálamo ------------------------------------------------------------------------------------

// O interruptor sono-vigília de Saper (passoSonoVigilia, do 05) com orexina, e dentro do sono um
// ciclo ultradiano NREM → REM de 90 min, com REM no último quarto de cada ciclo (o primeiro REM
// vem ~68 min depois de adormecer). O tempo é comprimido: 1 min de hipotálamo para cada 1 s de
// córtex (minutosPorSegundo), então um dia leva 1440 s de simulação. Saída estado: 0 vigília,
// 1 NREM, 2 REM. O sono é próximo do humano (um episódio consolidado por dia, ~5,6 h com estes
// parâmetros), enquanto os atrasos do perfil "roedor" são de rato: um sono polifásico de roedor
// (12–14 h em episódios curtos) fica para quando o padrão de sono importar.
function criarHipotalamo({ semente = 1, minutosPorSegundo = 1 } = {}) {
  const gerador = mulberry32(semente * 31 + 7);
  const e = { vigilia: 1, sono: 0, pressao: 0.1 };
  let minutosDormindo = 0;
  return {
    nome: "hipotálamo",
    nivel: "populacao",
    ligada: true,
    entradas: {},
    saidas: { estado: 0, vigilia: 1 },
    padrao: { estado: 0, vigilia: 1 },
    passo(dt) {
      const dtMin = (dt / 1000) * minutosPorSegundo;
      comGerador(gerador, () => passoSonoVigilia(e, dtMin, 1));
      if (e.vigilia > 0.5) {
        this.saidas.estado = 0;
        minutosDormindo = 0;
      } else {
        minutosDormindo += dtMin;
        this.saidas.estado = (minutosDormindo / 90) % 1 >= 0.75 ? 2 : 1;
      }
      this.saidas.vigilia = e.vigilia;
    },
    sondas() {
      return { estado: this.saidas.estado, pressao: e.pressao };
    },
  };
}

// --- Prosencéfalo basal ---------------------------------------------------------------------------------

// Acetilcolina tônica pelo estado (os níveis de estadosCerebrais: alta acordado e em REM, baixa em
// NREM), com τ de 2 s, mais uma parte fásica quando chega uma pista nova: a novidade do 05 (1 menos
// a familiaridade da pista, que cresce a cada exposição), decaindo em 200 ms. Saída limitada a 1,3.
function criarProsencefaloBasal() {
  let tonica = 1;
  let fasica = 0;
  let pistaAnterior = -1;
  const familiaridade = new Array(3).fill(0);
  return {
    nome: "prosencéfalo basal",
    nivel: "populacao",
    ligada: true,
    entradas: { estado: 0, pista: -1 },
    saidas: { acetilcolina: 1 },
    padrao: { acetilcolina: 1 },
    diario: [], // { pista, fasica } a cada pista nova
    passo(dt, t, { estado, pista }) {
      const alvo = estadosCerebrais[nomesDosEstados[estado]].acetilcolina;
      tonica = alvo + (tonica - alvo) * Math.exp(-dt / 2000);
      fasica *= Math.exp(-dt / 200);
      if (pista >= 0 && pista !== pistaAnterior) {
        const estimulo = [0, 1, 2].map((k) => (k === pista ? 1 : 0));
        const novo = novidade(estimulo, familiaridade);
        fasica += 0.3 * novo;
        this.diario.push({ pista, fasica: 0.3 * novo });
      }
      pistaAnterior = pista;
      this.saidas.acetilcolina = Math.min(1.3, tonica + fasica);
    },
    sondas() {
      return { acetilcolina: this.saidas.acetilcolina };
    },
  };
}

// --- Locus coeruleus -----------------------------------------------------------------------------------

// Noradrenalina tônica pelo estado (estadosCerebrais), τ de 2 s, e fásica pela surpresa da pista:
// o locus coeruleus conta as transições entre pistas dentro de um ensaio e, quando chega uma pista,
// a surpresa é 1 − P(pista | anterior), com P pelas contagens (mais 1, para nada começar com P = 0).
// A fásica soma a surpresa e decai em 200 ms. O começo de um ensaio (mais de 1,5 s sem pista) é a
// transição a partir de "nada".
function criarLocusCoeruleus() {
  let tonica = 0.5;
  let fasica = 0;
  let pistaAnterior = -1;
  let ultimaPista = -Infinity;
  let anteriorNoEnsaio = 3; // 3 = "nada"
  const contagens = Array.from({ length: 4 }, () => new Float64Array(3));
  return {
    nome: "locus coeruleus",
    nivel: "populacao",
    ligada: true,
    entradas: { estado: 0, pista: -1 },
    saidas: { noradrenalina: 0.5, noradrenalinaFasica: 0 },
    padrao: { noradrenalina: 0.5, noradrenalinaFasica: 0 },
    diario: [], // { pista, surpresa }
    passo(dt, t, { estado, pista }) {
      const alvo = estadosCerebrais[nomesDosEstados[estado]].noradrenalina;
      tonica = alvo + (tonica - alvo) * Math.exp(-dt / 2000);
      fasica *= Math.exp(-dt / 200);
      if (pista >= 0 && pista !== pistaAnterior) {
        if (t - ultimaPista > 1500) anteriorNoEnsaio = 3;
        const linhaDeContagens = contagens[anteriorNoEnsaio];
        const p = (linhaDeContagens[pista] + 1) / (somar(Array.from(linhaDeContagens)) + 3);
        const surpresa = 1 - p;
        fasica += surpresa;
        this.diario.push({ pista, surpresa });
        linhaDeContagens[pista]++;
        anteriorNoEnsaio = pista;
        ultimaPista = t;
      }
      pistaAnterior = pista;
      this.saidas.noradrenalina = tonica;
      this.saidas.noradrenalinaFasica = fasica;
    },
    sondas() {
      return { noradrenalina: this.saidas.noradrenalina, noradrenalinaFasica: this.saidas.noradrenalinaFasica };
    },
  };
}

// --- VTA ---------------------------------------------------------------------------------------------------

// Erro de diferença temporal (erroTD, do 05) com representação serial completa: o estado é (pista,
// passos de 100 ms desde que ela começou), até 2 s (o fim de um ensaio não chega ao próximo); fora
// disso o valor é 0. A cada 100 ms,
// δ = r + γ·V(s') − V(s) e V(s) += α·δ. A dopamina fásica soma max(0, δ) e decai em 200 ms; as
// pausas (δ < 0) aparecem no diário e nas sondas, mas não descem abaixo de zero no córtex.
// dopaminaComPausas soma o próprio δ, com sinal, e decai igual: é o que vai para o estriado, onde
// as pausas também ensinam. O começo de uma jogada do Pong (entrada jogada) conta como uma quarta
// pista, J, que só vai para a VTA.
function criarVTA({ alfa = 0.1, gamma = 0.98, passos = 20 } = {}) {
  const V = Array.from({ length: 4 }, () => new Float64Array(passos)); // pistas A, B, C e J
  let estado = null; // { pista, passo }
  let recompensaAcumulada = 0;
  let pistaAnterior = -1;
  let jogadaAnterior = 0;
  let inicioDaPista = 0;
  let dopamina = 0;
  let comPausas = 0;
  let delta = 0;
  const valor = (s) => (s ? V[s.pista][s.passo] : 0);
  return {
    nome: "VTA",
    nivel: "populacao",
    ligada: true,
    entradas: { pista: -1, recompensa: 0, jogada: 0 },
    saidas: { dopamina: 0, dopaminaComPausas: 0 },
    padrao: { dopamina: 0, dopaminaComPausas: 0 },
    diario: [], // { t, delta, evento }
    passosDoTD: [], // { t, delta } de todos os passos, para achar as pausas das omissões
    passo(dt, t, { pista, recompensa, jogada }) {
      recompensaAcumulada += recompensa;
      let evento = null;
      if (pista >= 0 && pista !== pistaAnterior) {
        inicioDaPista = t;
        evento = "ABC"[pista];
      }
      if (jogada > 0 && jogadaAnterior === 0) {
        inicioDaPista = t;
        evento = "J";
      }
      if (recompensa > 0) evento = "recompensa";
      pistaAnterior = pista;
      jogadaAnterior = jogada;
      dopamina *= Math.exp(-dt / 200);
      comPausas *= Math.exp(-dt / 200);
      if (Math.round(t) % 100 === 0 || evento) {
        // o novo estado: a pista mais recente e há quantos passos ela começou
        const k = Math.floor((t - inicioDaPista) / 100);
        const comeca = evento !== null && evento.length === 1;
        const ultima = comeca ? "ABCJ".indexOf(evento) : estado?.pista;
        const novo = ultima !== undefined && k < passos ? { pista: ultima, passo: comeca ? 0 : k } : null;
        delta = erroTD(recompensaAcumulada, valor(estado), valor(novo), gamma);
        if (estado) V[estado.pista][estado.passo] += alfa * delta;
        dopamina += Math.max(0, delta);
        comPausas += delta;
        if (evento) this.diario.push({ t, delta, evento });
        this.passosDoTD.push({ t, delta });
        estado = novo;
        recompensaAcumulada = 0;
      }
      this.saidas.dopamina = dopamina;
      this.saidas.dopaminaComPausas = comPausas;
    },
    sondas() {
      return { dopamina: this.saidas.dopamina, delta };
    },
    // os valores aprendidos de cada estado, para salvar em disco
    aprendido: () => ({ V: V.map((linha) => Array.from(linha)) }),
    carregar({ V: salvo }) {
      if (salvo.length !== V.length || salvo[0].length !== passos) throw new Error("a VTA salva tem outro número de estados");
      salvo.forEach((linha, k) => V[k].set(linha));
    },
  };
}

// --- Núcleos da base ---------------------------------------------------------------------------------

// Seleção de ação de Gurney, Prescott & Redgrave (2001), em taxa, com os pesos e limiares da
// implementação do Nengo (networks/actionselection.py). Cada canal i tem estriado D1 e D2, STN, GPe e
// GPi, cada um um integrador com vazamento (τ = 10 ms, escolha minha) com saída f(a − ε) linear por
// partes entre 0 e 1 (o Nengo não satura em 1; o artigo satura):
//   D1 = f(ws(1 + λ)·s_i − 0,2)   D2 = f(ws(1 − λ)·s_i − 0,2)   STN = f(wt·s_i − wg·GPe_i + 0,25)
//   GPe = f(wp·Σ STN − wm·D2_i + 0,2)   GPi = f(wp·Σ STN − wm·D1_i − we·GPe_i + 0,2)
// O STN é difuso (a soma de todos os canais entra em todos); o resto fica no canal. λ é a dopamina
// (0,2 tônica): mais dopamina, mais canais escolhidos; menos, nenhum. Um canal é escolhido quando o
// seu GPi cai abaixo do repouso (o GPi sem entrada nenhuma), e a alça é o quanto ele caiu.
const parametrosGPR = { ws: 1, wt: 1, wm: 1, wg: 1, wp: 0.9, we: 0.3, eStr: 0.2, eSTN: -0.25, eGPe: -0.2, eGPi: -0.2, lambda: 0.2, tau: 10 };
const camadasDoGPR = ["d1", "d2", "stn", "gpe", "gpi"];

function criarGPR(n) {
  const camadas = () => Object.fromEntries(camadasDoGPR.map((c) => [c, new Float64Array(n)]));
  return { a: camadas(), y: camadas() };
}

function passoGPR(g, s, lambda, dt, p = parametrosGPR) {
  const { a, y } = g;
  const n = s.length;
  let somaSTN = 0;
  for (let i = 0; i < n; i++) somaSTN += y.stn[i];
  const k = dt / p.tau;
  for (let i = 0; i < n; i++) {
    a.d1[i] += k * (p.ws * (1 + lambda) * s[i] - a.d1[i]);
    a.d2[i] += k * (p.ws * (1 - lambda) * s[i] - a.d2[i]);
    a.stn[i] += k * (p.wt * s[i] - p.wg * y.gpe[i] - a.stn[i]);
    a.gpe[i] += k * (p.wp * somaSTN - p.wm * y.d2[i] - a.gpe[i]);
    a.gpi[i] += k * (p.wp * somaSTN - p.wm * y.d1[i] - p.we * y.gpe[i] - a.gpi[i]);
  }
  const f = (x, limiar) => Math.min(1, Math.max(0, x - limiar));
  for (let i = 0; i < n; i++) {
    y.d1[i] = f(a.d1[i], p.eStr);
    y.d2[i] = f(a.d2[i], p.eStr);
    y.stn[i] = f(a.stn[i], p.eSTN);
    y.gpe[i] = f(a.gpe[i], p.eGPe);
    y.gpi[i] = f(a.gpi[i], p.eGPi);
  }
}

// O GPi depois de `ms` ms com saliências fixas e sem ruído
function equilibrioGPR(s, lambda = parametrosGPR.lambda, ms = 1000) {
  const g = criarGPR(s.length);
  for (let t = 0; t < ms; t++) passoGPR(g, s, lambda, 1);
  return Array.from(g.y.gpi);
}

const repousoDoGPi = equilibrioGPR(new Array(canaisDoCortex.length).fill(0))[0];
const alcaDoGPi = (gpi) => Math.min(1, Math.max(0, 1 - gpi / repousoDoGPi));

// Os núcleos da base do modo integrado: os 4 canais do córtex são 4 canais de ação.
//   Saliência: s_j = (Σ_i W_ji·x_i)·(1 + ξ_j), com x_i = (taxa do canal i do córtex − 5 Hz)/25 Hz,
//   entre 0 e 1,5. O estriado só lê o que passa da taxa de fundo (os neurônios espinhosos precisam
//   de muita entrada junta para sair do repouso); lendo a taxa inteira, o fundo dava saliência a
//   todos os canais, o ruído escolhia um e a alça o mantinha escolhido sozinha.
//   Exploração: ξ_j é um ruído de Ornstein-Uhlenbeck (σ = 0,5, τ = 300 ms, gerador próprio),
//   multiplicativo, então só age quando há entrada. Com as 4 ações recebendo a mesma pista, o GPR só
//   escolhe a que passa das outras por ~0,18 (o STN difuso inibe todas): um ruído aditivo pequeno
//   quase nunca dava escolha, e um grande daria escolhas no fundo.
//   Aprendizado: W (córtex → estriado) começa ao acaso entre 0,5 e 0,9 (na identidade, o canal da
//   pista sempre venceria e nenhuma outra ação seria tentada) e muda com três fatores:
//     τ_e·de_ji/dt = −e_ji + x_i·alca_j      dW_ji/dt = η·DA·e_ji      (W entre 0 e 1,5)
//   O pós é o canal que de fato venceu (a alça aberta, que no cérebro volta ao estriado do mesmo
//   canal pelo tálamo), e não a atividade de D1: na pista, D1 sobe em todos os canais, e a dopamina
//   da pista reforçava todas as ações juntas até nenhuma passar. DA é o erro de previsão da VTA com
//   as pausas (dopaminaComPausas).
//   Orçamento: depois de cada mudança, a soma das entradas de cada canal do estriado volta à do
//   começo (normalizarSoma, do 04). Sem isso a ação recompensada ia ao teto vindo de todos os canais
//   do córtex, inclusive os das outras pistas, e o acerto parava em ~40%.
//   Dopamina na seleção: λ = 0,2 + 0,2·DA, entre 0 e 0,6.
//   Controle: comDopamina = false deixa λ em 0,2 e W parado.
// A saída alca_j vai só para o canal j do córtex (pelo tálamo) e para o efetor no ambiente: a escolha
// não chega a nenhuma outra região.
const parametrosDosNucleosDaBase = {
  taxaDeFundo: 5, faixaDeTaxa: 25, wInicial: [0.5, 0.9], wMax: 1.5, tauElegibilidade: 1000, eta: 10, ganhoDaDopamina: 0.2, ruido: 0.5, tauRuido: 300,
  orcamento: "por acao", // ou "por entrada" (ver criarNucleosDaBase)
};

// acoes: os canais que podem ser escolhidos (null: todos). Os outros não recebem saliência, então
// nunca abrem a alça nem aprendem.
// canaisDeEntrada: os canais do córtex que chegam ao estriado (null: todos). Os outros começam com
// peso 0 e não entram nem na saliência nem na elegibilidade.
// orcamento: "por acao" (o padrão) mantém a soma das entradas de cada canal do estriado; "por entrada"
// mantém a soma do que cada canal de entrada manda para as ações, então ele sempre aciona alguma
// ação. No Pong, por ação deixava uma armadilha: se as duas ações perdiam o peso vindo de "bola
// abaixo" logo no começo, essa entrada não acionava mais nada, o ruído multiplicativo sumia junto, e
// a rede nunca mais tentava (2 de 5 corridas presas em ~13% de rebatidas por 90 min).
// nCanais: quantos canais o córtex tem (um canal do estriado para cada); com outro número que não 4,
// o repouso do GPi (a referência da alça) é recalculado, porque o STN difuso soma todos os canais.
function criarNucleosDaBase({ semente = 1, comDopamina = true, acoes = null, canaisDeEntrada = null, orcamento: tipoDeOrcamento = null, nCanais = canaisDoCortex.length, p: parametros = parametrosDosNucleosDaBase } = {}) {
  const p = tipoDeOrcamento ? { ...parametros, orcamento: tipoDeOrcamento } : parametros;
  const n = nCanais;
  const indices = Array.from({ length: n }, (_, k) => k);
  const ehAcao = indices.map((j) => acoes === null || acoes.includes(j));
  const ehEntrada = indices.map((i) => canaisDeEntrada === null || canaisDeEntrada.includes(i));
  const repouso = n === canaisDoCortex.length ? repousoDoGPi : equilibrioGPR(new Array(n).fill(0))[0];
  const alcaDoGPiAqui = (gpi) => Math.min(1, Math.max(0, 1 - gpi / repouso));
  const gerador = mulberry32(semente * 104729 + 3);
  // W[pós j][pré i]; o sorteio é feito mesmo nas entradas desligadas, para o gerador seguir igual
  const W = Array.from({ length: n }, () =>
    Float64Array.from({ length: n }, (_, i) => {
      const w = p.wInicial[0] + (p.wInicial[1] - p.wInicial[0]) * gerador();
      return ehEntrada[i] ? w : 0;
    }),
  );
  const orcamento = W.map((linha) => somar(Array.from(linha)));
  const orcamentoDaEntrada = indices.map((i) => somar(W.filter((_, j) => ehAcao[j]).map((linha) => linha[i])));
  const e = Array.from({ length: n }, () => new Float64Array(n));
  const ruido = new Float64Array(n);
  const x = new Float64Array(n);
  const s = new Float64Array(n);
  const alca = new Float64Array(n);
  const gpr = criarGPR(n);
  const chavesDoCanal = indices.map((k) => `canal${k}`);
  const chavesDaAlca = indices.map((k) => `alca${k}`);
  const porCanal = (chaves, valor) => Object.fromEntries(chaves.map((chave) => [chave, valor]));
  return {
    nome: "núcleos da base",
    nivel: "populacao",
    ligada: true,
    entradas: { ...porCanal(chavesDoCanal, 0), dopamina: 0 },
    saidas: porCanal(chavesDaAlca, 0),
    padrao: porCanal(chavesDaAlca, 0),
    W,
    wInicial: W.map((linha) => Float64Array.from(linha)),
    passo(dt, t, entradas) {
      const da = comDopamina ? entradas.dopamina : 0;
      const lambda = Math.min(0.6, Math.max(0, parametrosGPR.lambda + p.ganhoDaDopamina * da));
      const decaiRuido = Math.exp(-dt / p.tauRuido);
      const passoDoRuido = p.ruido * Math.sqrt(1 - decaiRuido * decaiRuido);
      comGerador(gerador, () => {
        for (let j = 0; j < n; j++) ruido[j] = ruido[j] * decaiRuido + passoDoRuido * gaussiana();
      });
      for (let i = 0; i < n; i++) x[i] = ehEntrada[i] ? Math.min(1.5, Math.max(0, (entradas[chavesDoCanal[i]] - p.taxaDeFundo) / p.faixaDeTaxa)) : 0;
      for (let j = 0; j < n; j++) {
        let soma = 0;
        if (ehAcao[j]) for (let i = 0; i < n; i++) soma += W[j][i] * x[i];
        s[j] = Math.max(0, soma * (1 + ruido[j]));
      }
      passoGPR(gpr, s, lambda, dt);
      const decai = Math.exp(-dt / p.tauElegibilidade);
      for (let j = 0; j < n; j++) {
        alca[j] = alcaDoGPiAqui(gpr.y.gpi[j]);
        this.saidas[chavesDaAlca[j]] = alca[j];
        for (let i = 0; i < n; i++) {
          const alvo = x[i] * alca[j];
          e[j][i] = alvo + (e[j][i] - alvo) * decai;
          if (da !== 0) W[j][i] = Math.min(p.wMax, Math.max(0, W[j][i] + (p.eta * da * e[j][i] * dt) / 1000));
        }
        if (da !== 0 && p.orcamento === "por acao" && W[j].some((w) => w > 0)) {
          normalizarSoma(W[j], orcamento[j]);
          for (let i = 0; i < n; i++) W[j][i] = Math.min(p.wMax, W[j][i]);
        }
      }
      if (da !== 0 && p.orcamento === "por entrada") {
        for (let i = 0; i < n; i++) {
          if (!ehEntrada[i]) continue;
          let soma = 0;
          for (let j = 0; j < n; j++) if (ehAcao[j]) soma += W[j][i];
          if (soma > 0) for (let j = 0; j < n; j++) if (ehAcao[j]) W[j][i] = Math.min(p.wMax, (W[j][i] * orcamentoDaEntrada[i]) / soma);
        }
      }
    },
    sondas() {
      return { ...this.saidas, ...Object.fromEntries(Array.from(gpr.y.gpi, (g, j) => [`gpi${j}`, g])) };
    },
    // os pesos córtex → estriado, para salvar em disco; o orçamento continua o desta semente
    aprendido: () => ({ W: W.map((linha) => Array.from(linha)) }),
    carregar({ W: salvo }) {
      salvo.forEach((linha, j) => W[j].set(linha));
      for (const linha of e) linha.fill(0);
    },
  };
}

// --- Montagem, testes de saúde e linha de comando -------------------------------------------------

// As regiões, na ordem em que entram no modo integrado (o ambiente está sempre ligado)
const ordemDasRegioes = ["cortex", "hipotalamo", "prosencefaloBasal", "locusCoeruleus", "vta", "nucleosDaBase"];

// tarefa: "pistas" (A, B ou C e a recompensa depois de B), "escolha" (a recompensa só vem se a
// resposta depois de B foi a certa) ou "pong" (contra o v1; ver criarPong e cerebroNoPong).
// comDopamina: false tira a dopamina dos núcleos da base.
function montarIntegrado(ligadas, { semente = 1, perfil = "roedor", nivelCortex = "spikes", noSono = [], tarefa = "pistas", comDopamina = true } = {}) {
  semear(semente);
  const pong = tarefa === "pong" ? cerebroNoPong : null;
  const regioes = {
    ambiente: pong ? criarPong(semente) : criarAmbiente(semente, { tarefa }),
    cortex: criarCortex({ nivel: nivelCortex, noSono, ...(pong ? { canais: pong.canais } : {}) }),
    hipotalamo: criarHipotalamo({ semente }),
    prosencefaloBasal: criarProsencefaloBasal(),
    locusCoeruleus: criarLocusCoeruleus(),
    // no Pong a cadeia de estados da VTA vai a 4 s, para cobrir a volta da bola até a jogada seguinte:
    // com 2 s, cada começo de jogada chegava sem previsão, e a dopamina dele reforçava ao acaso o que
    // a raquete estivesse fazendo
    vta: criarVTA(tarefa === "pong" ? { passos: 40 } : {}),
    // No Pong, só subir e descer são ações, e só os sentidos chegam ao estriado. Com os sentidos
    // também como ações, eles viravam "ficar parado" e competiam com mover. Com as ações também como
    // entradas, a alça de uma ação excitava o próprio canal motor, esse eco voltava ao estriado,
    // ganhava crédito a cada rebatida e, pelo orçamento, tirava o peso da bola: depois de ~1 h de
    // jogo o mapa sumia e a raquete parava.
    nucleosDaBase: criarNucleosDaBase({
      semente,
      comDopamina,
      ...(pong ? { acoes: pong.acoes, canaisDeEntrada: pong.entradas, orcamento: pong.orcamento, nCanais: pong.canais.length } : {}),
    }),
  };
  for (const nome of ordemDasRegioes) regioes[nome].ligada = ligadas.includes(nome);
  return new CerebroIntegrado(regioes, { perfil, tarefa, ...(pong ? { nCanais: pong.canais.length, nSensores: pong.entradas.length } : {}) });
}

// Roda um dia comprimido (ou `segundos`) e junta as medidas dos testes: médias por estado (a cada
// 10 ms), os diários das regiões e o córtex no começo e no fim. Grava as sondas a cada 100 ms.
// Com os núcleos da base, a tarefa padrão é a de escolha. Junta também uma impressão digital das
// saídas, a cada ms, das regiões que não são o córtex nem os núcleos da base (para o teste de que a
// escolha não chega a outra região) e a fração do tempo com uma alça aberta longe das pistas.
function rodarIntegrado(ligadas, opcoes = {}) {
  const { segundos = 1440, arquivoDeSondas = null } = opcoes;
  const tarefa = opcoes.tarefa ?? (ligadas.includes("nucleosDaBase") ? "escolha" : "pistas");
  const integrado = montarIntegrado(ligadas, { ...opcoes, tarefa });
  const { regioes } = integrado;
  const outras = Object.entries(regioes).filter(([nome]) => nome !== "cortex" && nome !== "nucleosDaBase").map(([, regiao]) => regiao);
  const digital = new Float64Array(1);
  const bits = new Uint32Array(digital.buffer);
  let impressao = 2166136261;
  const misturar = (valor) => {
    digital[0] = valor;
    impressao = Math.imul(impressao ^ bits[0], 16777619);
    impressao = Math.imul(impressao ^ bits[1], 16777619);
  };
  const alcaForaDasPistas = { aberta: 0, total: 0 };
  let ultimaPista = -Infinity;
  const pesosDaBaseNoInicio = regioes.nucleosDaBase.wInicial;
  const porEstado = nomesDosEstados.map(() => ({ ms: 0, taxaE: 0, taxaI: 0, acetilcolina: 0, noradrenalina: 0, dopamina: 0, taxaMaxima: 0, nan: 0 }));
  const sondas = arquivoDeSondas
    ? new Sondas(arquivoDeSondas, {
        t: () => integrado.t,
        ...Object.fromEntries(
          Object.entries(regioes).flatMap(([nome, regiao]) => Object.keys(regiao.sondas()).map((chave) => [`${nome}.${chave}`, () => (regiao.ligada ? regiao.sondas()[chave] : null)])),
        ),
      })
    : null;
  const pesosNoInicio = regioes.cortex.pesos();
  const canal0 = { comA: 0, msComA: 0, semPista: 0, msSemPista: 0 };
  // a cada troca entre vigília e sono: os pesos do córtex e as taxas médias do episódio que acabou
  const transicoes = [];
  let acordadoAntes = true;
  let inicioDoOutroLado = null; // a troca só conta se o novo estado durar 1 s (1 min de hipotálamo)
  let episodio = { taxaE: 0, taxaI: 0, n: 0 };
  const relogio = performance.now();
  const total = segundos * 1000;
  for (let ms = 1; ms <= total; ms++) {
    integrado.passo(1);
    for (const regiao of outras) if (regiao.ligada) for (const chave in regiao.saidas) misturar(regiao.saidas[chave]);
    if (ms % 10 !== 0) continue;
    if (regioes.nucleosDaBase.ligada) {
      if (regioes.cortex.entradas.pista >= 0) ultimaPista = ms;
      else if (ms - ultimaPista > 1500) {
        alcaForaDasPistas.total++;
        if (canaisDoCortex.some((_, k) => regioes.cortex.entradas[`alca${k}`] > 0.5)) alcaForaDasPistas.aberta++;
      }
    }
    const estado = regioes.hipotalamo.ligada ? regioes.hipotalamo.saidas.estado : 0;
    const acumulado = porEstado[estado];
    const { taxaE, taxaI } = regioes.cortex.saidas;
    const entradas = regioes.cortex.entradas;
    acumulado.ms += 10;
    acumulado.taxaE += taxaE * 10;
    acumulado.taxaI += taxaI * 10;
    acumulado.acetilcolina += entradas.acetilcolina * 10;
    acumulado.noradrenalina += entradas.noradrenalina * 10;
    acumulado.dopamina += entradas.dopamina * 10;
    if (!Number.isFinite(taxaE)) acumulado.nan++;
    acumulado.taxaMaxima = Math.max(acumulado.taxaMaxima, taxaE);
    if (regioes.cortex.entradas.pista === 0) {
      canal0.comA += regioes.cortex.saidas.canal0;
      canal0.msComA += 10;
    } else if (regioes.cortex.entradas.pista === -1) {
      canal0.semPista += regioes.cortex.saidas.canal0;
      canal0.msSemPista += 10;
    }
    if (sondas && ms % 100 === 0) sondas.amostrar();
    episodio.taxaE += taxaE;
    episodio.taxaI += taxaI;
    episodio.n++;
    if ((estado === 0) === acordadoAntes) inicioDoOutroLado = null;
    else {
      inicioDoOutroLado ??= ms;
      if (ms - inicioDoOutroLado >= 1000) {
        transicoes.push({ t: inicioDoOutroLado / 1000, adormeceu: estado !== 0, pesos: regioes.cortex.pesos(), taxaE: episodio.taxaE / episodio.n, taxaI: episodio.taxaI / episodio.n });
        episodio = { taxaE: 0, taxaI: 0, n: 0 };
        acordadoAntes = estado === 0;
        inicioDoOutroLado = null;
      }
    }
  }
  sondas?.descarregar();
  const medidasPorEstado = porEstado.map((a) => ({
    fracaoDoTempo: a.ms / total,
    taxaE: a.taxaE / a.ms,
    taxaI: a.taxaI / a.ms,
    acetilcolina: a.acetilcolina / a.ms,
    noradrenalina: a.noradrenalina / a.ms,
    dopamina: a.dopamina / a.ms,
    taxaMaxima: a.taxaMaxima,
    nan: a.nan,
  }));
  return {
    ligadas,
    segundosDeRelogio: (performance.now() - relogio) / 1000,
    porEstado: medidasPorEstado,
    pesosNoInicio,
    pesosNoFim: regioes.cortex.pesos(),
    ambiente: regioes.ambiente.diario,
    prosencefaloBasal: regioes.prosencefaloBasal.diario,
    locusCoeruleus: regioes.locusCoeruleus.diario,
    vta: regioes.vta.diario,
    passosDoTD: regioes.vta.passosDoTD,
    canal0: { comA: (10 * canal0.comA) / canal0.msComA, semPista: (10 * canal0.semPista) / canal0.msSemPista },
    transicoes,
    tarefa,
    impressao: impressao >>> 0,
    alcaForaDasPistas: alcaForaDasPistas.aberta / alcaForaDasPistas.total,
    pesosDaBase: { inicio: pesosDaBaseNoInicio, fim: regioes.nucleosDaBase.W.map((linha) => Float64Array.from(linha)) },
    vias: integrado.vias.map(({ origem, saida, destino, entrada, atraso }) => ({ origem, saida, destino, entrada, atraso })),
  };
}

// Saúde do córtex: em cada estado em que passou tempo, taxa E entre 0,2 e 20 Hz, nenhum NaN, pesos
// E→E com menos de 20% no teto e média entre 1/4 e 4× a do começo
function saudeDoCortex(r) {
  const problemas = [];
  r.porEstado.forEach((e, k) => {
    if (e.fracaoDoTempo === 0) return;
    if (e.nan > 0) problemas.push(`NaN em ${nomesDosEstados[k]}`);
    if (!(e.taxaE >= 0.2 && e.taxaE <= 20)) problemas.push(`taxa E de ${e.taxaE.toFixed(1)} Hz em ${nomesDosEstados[k]}`);
  });
  const { pesosNoInicio: a, pesosNoFim: b } = r;
  if (Number.isFinite(b.noTeto) && b.noTeto > 0.2) problemas.push(`${(100 * b.noTeto).toFixed(0)}% dos pesos no teto`);
  const razao = (b.dentro * 0.5 + b.fora * 0.5) / (a.dentro * 0.5 + a.fora * 0.5);
  if (Number.isFinite(razao) && !(razao > 0.25 && razao < 4)) problemas.push(`peso médio ${razao.toFixed(2)}× o inicial`);
  return problemas;
}

// A alça vista pelo córtex: um córtex sozinho recebe a alça toda aberta em um canal por vez (500 ms
// abertos, 500 ms fechados, 4 voltas pelos canais) e devolve, para cada canal aberto k, quanto a taxa
// de cada canal m subiu sobre a dos 500 ms fechados de antes (médias dos últimos 300 ms de cada fase)
function testarAlcaNoCortex({ nivel = "spikes", semente = 1 } = {}) {
  semear(semente);
  const cortex = criarCortex({ nivel });
  const n = canaisDoCortex.length;
  const subida = Array.from({ length: n }, () => new Float64Array(n));
  let t = 0;
  const fase = (aberto) => {
    for (let k = 0; k < n; k++) cortex.entradas[`alca${k}`] = k === aberto ? 1 : 0;
    const soma = new Float64Array(n);
    for (let ms = 0; ms < 500; ms++) {
      cortex.passo(1, ++t, cortex.entradas);
      if (ms >= 200) for (let m = 0; m < n; m++) soma[m] += cortex.saidas[`canal${m}`] / 300;
    }
    return soma;
  };
  fase(-1);
  fase(-1);
  const voltas = 4;
  for (let volta = 0; volta < voltas; volta++) {
    for (let k = 0; k < n; k++) {
      const antes = fase(-1);
      const durante = fase(k);
      for (let m = 0; m < n; m++) subida[k][m] += (durante[m] - antes[m]) / voltas;
    }
  }
  return subida;
}

// A assinatura de cada região: o que ela tem de fazer para entrar
const assinaturas = {
  cortex: (r) => [
    [`o canal 0 responde à pista A: ${r.canal0.comA.toFixed(1)} Hz com ela, ${r.canal0.semPista.toFixed(1)} Hz sem pista`, r.canal0.comA > 2 * r.canal0.semPista],
  ],
  hipotalamo: (r) => {
    const [, n, rem] = r.porEstado.map((e) => e.fracaoDoTempo);
    const sono = n + rem;
    return [
      // o interruptor do 05 dorme ~5,8 h por ciclo; o critério de 6–10 h (humano) foi trocado por
      // 4–8 h quando se decidiu manter o sono do 05
      [`dorme ${(24 * sono).toFixed(1)} h do dia (esperado 4–8 h, o do interruptor do 05)`, sono * 24 >= 4 && sono * 24 <= 8],
      [`REM é ${(100 * rem / Math.max(sono, 1e-9)).toFixed(0)}% do sono (esperado 15–30%)`, rem / sono >= 0.15 && rem / sono <= 0.3],
    ];
  },
  prosencefaloBasal: (r) => {
    const [v, n, rem] = r.porEstado;
    const primeiras = r.prosencefaloBasal.slice(0, 3).map((d) => d.fasica);
    const ultimas = r.prosencefaloBasal.slice(-3).map((d) => d.fasica);
    return [
      [`ACh acordado ${v.acetilcolina.toFixed(2)} · NREM ${n.acetilcolina.toFixed(2)} · REM ${rem.acetilcolina.toFixed(2)} (alta, baixa, alta)`, v.acetilcolina > 0.8 && (n.fracaoDoTempo === 0 || n.acetilcolina < 0.3)],
      [`ACh fásica nas primeiras pistas ${media(primeiras).toFixed(2)} e nas últimas ${media(ultimas).toFixed(3)} (a novidade se habitua)`, media(ultimas) < 0.5 * media(primeiras)],
    ];
  },
  locusCoeruleus: (r) => {
    const segundaMetade = r.locusCoeruleus.slice(Math.floor(r.locusCoeruleus.length / 2));
    const deB = segundaMetade.filter((d) => d.pista === 1).map((d) => d.surpresa);
    const deC = segundaMetade.filter((d) => d.pista === 2).map((d) => d.surpresa);
    const [v, n] = r.porEstado;
    return [
      [`NA fásica após C (rara) ${media(deC).toFixed(2)} · após B (comum) ${media(deB).toFixed(2)}`, media(deC) > 2 * media(deB)],
      [`NA tônica acordado ${v.noradrenalina.toFixed(2)} · NREM ${n.noradrenalina.toFixed(2)}`, n.fracaoDoTempo === 0 || v.noradrenalina > n.noradrenalina],
    ];
  },
  vta: (r) => {
    const diario = r.vta;
    const deTipo = (tipo, parte) => {
      const lista = diario.filter((d) => d.evento === tipo).map((d) => d.delta);
      const n = Math.max(1, Math.floor(lista.length / 5));
      return parte === "inicio" ? media(lista.slice(0, n)) : media(lista.slice(-n));
    };
    const naPistaInicio = deTipo("A", "inicio");
    const naPistaFim = deTipo("A", "fim");
    const naRecompensaInicio = deTipo("recompensa", "inicio");
    const naRecompensaFim = deTipo("recompensa", "fim");
    const latencia = latenciaSensorial.roedor;
    const naOmissao = r.ambiente
      .filter((d) => d.tipo === "omissao")
      .slice(-10)
      .map((d) => r.passosDoTD.find((passo) => passo.t >= d.t + latencia)?.delta ?? NaN);
    return [
      [`δ na pista A: ${naPistaInicio.toFixed(2)} → ${naPistaFim.toFixed(2)} (primeiros → últimos 20% dos ensaios)`, naPistaFim > naPistaInicio + 0.2],
      [`δ na recompensa: ${naRecompensaInicio.toFixed(2)} → ${naRecompensaFim.toFixed(2)}`, naRecompensaFim < naRecompensaInicio - 0.2],
      [`δ na pista C (sem recompensa): ${deTipo("C", "fim").toFixed(2)} (pausa, < 0)`, deTipo("C", "fim") < 0],
      [`δ nas últimas omissões: ${media(naOmissao).toFixed(2)} (pausa, < 0)`, media(naOmissao) < 0],
    ];
  },
  // r.testeDaAlca (testarAlcaNoCortex) e r.controle (as impressões digitais das outras regiões sem os
  // núcleos da base e com eles na tarefa de pistas) vêm de demonstracaoIntegrado
  nucleosDaBase: (r) => {
    const escolhidos = (s, lambda) => equilibrioGPR(s, lambda).flatMap((g, j) => (alcaDoGPi(g) > 0.5 ? [j] : []));
    const lista = (js) => (js.length ? `canal ${js.join(" e ")}` : "nenhum");
    const porcento = (x) => `${(100 * x).toFixed(0)}%`;
    const forte = [escolhidos([0.3, 0.6, 0.2, 0.1]), escolhidos([0.6, 0.3, 0.2, 0.1])];
    const porDopamina = [0, 0.2, 0.5].map((lambda) => escolhidos([0.6, 0.4, 0, 0], lambda));
    const respostas = r.ambiente.filter((d) => d.tipo === "resposta" && d.pista === 1);
    const quinto = Math.max(1, Math.floor(respostas.length / 5));
    const acerto = (parte) => parte.filter((d) => d.acao === 3).length / parte.length;
    const [inicio, fim] = [acerto(respostas.slice(0, quinto)), acerto(respostas.slice(-quinto))];
    const saidas = r.vias.filter((via) => via.origem === "nucleosDaBase");
    const soParaOProprioCanal = saidas.every((via) => ["cortex", "ambiente"].includes(via.destino) && via.entrada === via.saida);
    const n = canaisDoCortex.length;
    const subidas = r.testeDaAlca ?? [];
    const propria = media(subidas.map((linha, k) => linha[k]));
    const outros = media(subidas.flatMap((linha, k) => Array.from(linha).filter((_, m) => m !== k)));
    const { semNucleos, comNucleos } = r.controle ?? {};
    return [
      [`escolhe o canal mais forte: saliências 0,3/0,6/0,2/0,1 → ${lista(forte[0])}; 0,6/0,3/0,2/0,1 → ${lista(forte[1])}`, forte[0].join() === "1" && forte[1].join() === "0"],
      [
        `a dopamina muda quantos passam: 0,6/0,4/0/0 com λ = 0 → ${lista(porDopamina[0])}; 0,2 → ${lista(porDopamina[1])}; 0,5 → ${lista(porDopamina[2])}`,
        porDopamina[0].length === 0 && porDopamina[1].join() === "0" && porDopamina[2].length === 2,
      ],
      [`ação 3 (a recompensada) depois de B: ${porcento(inicio)} nos primeiros 20% dos ${respostas.length} ensaios com B → ${porcento(fim)} nos últimos`, fim > inicio + 0.2],
      [`as ${saidas.length} vias que saem dos núcleos da base vão só para o mesmo canal do córtex (${n}) e para o efetor (${n})`, soParaOProprioCanal && saidas.length === 2 * n],
      [`a alça toda aberta sobe o próprio canal do córtex em ${propria.toFixed(1)} Hz e cada um dos outros em ${outros.toFixed(1)} Hz`, propria > 2 && outros < 0.2 * propria],
      [
        `com a recompensa independente da ação, as saídas das outras regiões a cada ms são idênticas sem e com os núcleos da base (impressões ${semNucleos} e ${comNucleos})`,
        semNucleos !== undefined && semNucleos === comNucleos,
      ],
      [`alça aberta longe das pistas (mais de 1,5 s depois): ${porcento(r.alcaForaDasPistas)} do tempo (a escolha não se mantém sozinha)`, r.alcaForaDasPistas < 0.1],
    ];
  },
};

function imprimirComparacao(nova, sem, com) {
  const linhaPorEstado = (rotulo, ler, casas = 1) =>
    linha(rotulo, nomesDosEstados.map((nome, k) => `${nome} ${[sem, com].map((r) => (r.porEstado[k].fracaoDoTempo > 0 ? ler(r.porEstado[k]).toFixed(casas) : "—")).join(" → ")}`).join(" · "));
  console.log(`\n${nova}: sem → com (${sem.segundosDeRelogio.toFixed(0)} s e ${com.segundosDeRelogio.toFixed(0)} s de relógio)`);
  linhaPorEstado("fração do tempo", (e) => e.fracaoDoTempo, 2);
  linhaPorEstado("taxa E do córtex (Hz)", (e) => e.taxaE);
  linhaPorEstado("taxa I do córtex (Hz)", (e) => e.taxaI);
  linhaPorEstado("acetilcolina no córtex", (e) => e.acetilcolina, 2);
  linhaPorEstado("noradrenalina no córtex", (e) => e.noradrenalina, 2);
  linhaPorEstado("dopamina no córtex", (e) => e.dopamina, 3);
  const pesos = (r) => `canal ${r.pesosNoFim.dentro.toFixed(4)} · fora ${r.pesosNoFim.fora.toFixed(4)} · teto ${(100 * r.pesosNoFim.noTeto).toFixed(1)}%`;
  linha("pesos E→E no fim (sem)", pesos(sem));
  linha("pesos E→E no fim (com)", pesos(com));
}

// Os pesos do córtex a cada vez que o hipotálamo adormece e acorda, e quanto mudaram em cada noite
// e em cada dia
function imprimirDias(r) {
  const f = (x, c = 4) => (Number.isFinite(x) ? x.toFixed(c) : "—");
  const hora = (t) => `dia ${Math.floor(t / 1440) + 1}, ${String(Math.floor((t % 1440) / 60)).padStart(2, "0")}h${String(Math.floor(t % 60)).padStart(2, "0")}`;
  console.log(`  ${r.segundosDeRelogio.toFixed(0)} s de relógio`);
  console.log(`  pesos E→E (média): fora dos canais · dentro dos canais · no teto · I→E; taxa E e I do episódio que terminou`);
  linha("  início", `fora ${f(r.pesosNoInicio.fora)} · dentro ${f(r.pesosNoInicio.dentro)} · teto ${f(100 * r.pesosNoInicio.noTeto, 1)}% · I→E ${f(r.pesosNoInicio.ie)}`);
  let anterior = r.pesosNoInicio;
  for (const transicao of r.transicoes) {
    const { pesos: p } = transicao;
    const variacao = (100 * (p.fora - anterior.fora)) / anterior.fora;
    linha(
      `  ${transicao.adormeceu ? "adormece" : "acorda"} (${hora(transicao.t)})`,
      `fora ${f(p.fora)} (${variacao >= 0 ? "+" : ""}${f(variacao, 1)}% no ${transicao.adormeceu ? "dia" : "sono"}) · dentro ${f(p.dentro)} · teto ${f(100 * p.noTeto, 1)}% · ` +
        `I→E ${f(p.ie)} · E ${f(transicao.taxaE, 1)} Hz · I ${f(transicao.taxaI, 1)} Hz`,
    );
    anterior = p;
  }
}

// Os pesos córtex → estriado no começo e no fim: linha = canal do estriado (a ação), coluna = canal
// do córtex
function imprimirPesosDaBase({ inicio, fim }, rotulo = "pesos córtex → estriado") {
  console.log(`  ${rotulo} (linha: ação; coluna: canal do córtex 0 1 2 3), começo → fim`);
  inicio.forEach((linhaW, j) => {
    const formatar = (w) => Array.from(w, (x) => x.toFixed(2).padStart(5)).join("");
    linha(`    ação ${j}`, `${formatar(linhaW)}   →  ${formatar(fim[j])}`);
  });
}

// --- Experimentos de aprendizado: a tarefa de escolha e o Pong ------------------------------------
// Acordado (hipotálamo desligado, então o sono e a decisão pendente sobre a homeostase no sono não
// entram), com córtex, prosencéfalo basal, locus coeruleus, VTA e núcleos da base, em duas condições:
// com dopamina e sem dopamina nos núcleos da base (o controle; λ fica em 0,2 e W não muda). Cada
// simulação grava um resumo em resultados/integrado/<experimento>/, e --analisar refaz o resumo de
// todas as que estão lá, então as sementes podem rodar em processos separados.
const condicoesDoAprendizado = { "com dopamina": { comDopamina: true }, "sem dopamina": { comDopamina: false } };
const ligadasNoAprendizado = ["cortex", "prosencefaloBasal", "locusCoeruleus", "vta", "nucleosDaBase"];

// O que sai de cada simulação: os eventos que medem o desempenho e os pesos córtex → estriado
function resumirAprendizado(experimento, condicao, semente, r) {
  const tipos = experimento === "pong" ? ["rebatida", "erro"] : ["resposta"];
  return {
    experimento,
    condicao,
    semente,
    segundosDeRelogio: Math.round(r.segundosDeRelogio),
    taxaE: r.porEstado[0].taxaE,
    eventos: r.ambiente.filter((d) => tipos.includes(d.tipo)),
    pesosDaBase: { inicio: r.pesosDaBase.inicio.map((l) => Array.from(l)), fim: r.pesosDaBase.fim.map((l) => Array.from(l)) },
  };
}

// Pong só com o ambiente e uma política fixa, para comparar: a raquete parada no meio, ações ao acaso
// (uma nova a cada 200 ms: subir, descer ou ficar) e um seguidor que sempre anda na direção da bola
function pongSemCerebro(politica, semente, segundos) {
  const pong = criarPong(semente);
  const sortear = mulberry32(semente * 31 + 5);
  let acao = 0;
  for (let t = 1; t <= segundos * 1000; t++) {
    if (politica === "ao acaso" && t % 200 === 1) acao = Math.floor(3 * sortear()) - 1;
    if (politica === "seguidor") acao = pong.saidas.sensor0 > 0.02 ? 1 : pong.saidas.sensor1 > 0.02 ? -1 : 0;
    pong.entradas.alca2 = acao === 1 ? 1 : 0;
    pong.entradas.alca3 = acao === -1 ? 1 : 0;
    pong.passo(1, t, pong.entradas);
  }
  const resultados = pong.diario.filter((d) => d.tipo === "rebatida" || d.tipo === "erro");
  return { acerto: resultados.filter((d) => d.tipo === "rebatida").length / resultados.length, jogadas: resultados.length };
}

// Acertos por quinto do treino: na escolha, a fração das respostas depois de B que foram a ação 3;
// no Pong, a fração das jogadas rebatidas
function curvaDeAprendizado(resumo, partes = 5) {
  const acertou = resumo.experimento === "pong" ? (d) => d.tipo === "rebatida" : (d) => d.acao === 3;
  const eventos = resumo.experimento === "pong" ? resumo.eventos : resumo.eventos.filter((d) => d.pista === 1);
  const tamanho = eventos.length / partes;
  return Array.from({ length: partes }, (_, k) => {
    const parte = eventos.slice(Math.round(k * tamanho), Math.round((k + 1) * tamanho));
    return parte.filter(acertou).length / parte.length;
  });
}

function imprimirAprendizado(experimento, resumos, sementes) {
  const porcento = (x, casas = 0) => `${(100 * x).toFixed(casas)}%`;
  const resumo = (valores) => `${porcento(media(valores))} ± ${porcento(desvioPadrao(valores))}`;
  const quintos = ["1º", "2º", "3º", "4º", "5º"];
  console.log(`\n${experimento === "pong" ? "Pong" : "Escolha depois de B"}: acertos por quinto do treino, média ± desvio entre sementes`);
  for (const condicao of Object.keys(condicoesDoAprendizado)) {
    const lista = resumos.filter((r) => r.condicao === condicao).sort((a, b) => a.semente - b.semente);
    if (lista.length === 0) continue;
    const curvas = lista.map((r) => curvaDeAprendizado(r));
    const n = experimento === "pong" ? lista.map((r) => r.eventos.length) : lista.map((r) => r.eventos.filter((d) => d.pista === 1).length);
    console.log(`\n  ${condicao}: sementes ${lista.map((r) => r.semente).join(", ")} · ${media(n).toFixed(0)} ${experimento === "pong" ? "jogadas" : "ensaios com B"} por semente · ${media(lista.map((r) => r.segundosDeRelogio)).toFixed(0)} s de relógio · córtex ${media(lista.map((r) => r.taxaE)).toFixed(1)} Hz`);
    quintos.forEach((nome, k) => linha(`    ${nome} quinto`, `${resumo(curvas.map((c) => c[k]))}   (${curvas.map((c) => porcento(c[k])).join(" ")})`));
    if (experimento === "escolha") {
      const ultimas = lista.map((r) => {
        const comB = r.eventos.filter((d) => d.pista === 1);
        return comB.slice(-Math.floor(comB.length / 5));
      });
      const fracao = (acao) => resumo(ultimas.map((u) => u.filter((d) => d.acao === acao).length / u.length));
      linha("    respostas no último quinto", `${[0, 1, 2, 3].map((a) => `ação ${a}: ${fracao(a)}`).join(" · ")} · nenhuma: ${fracao(-1)}`);
    }
    const mediaDosPesos = (momento) => lista[0].pesosDaBase[momento].map((linhaW, j) => linhaW.map((_, i) => media(lista.map((r) => r.pesosDaBase[momento][j][i]))));
    imprimirPesosDaBase({ inicio: mediaDosPesos("inicio"), fim: mediaDosPesos("fim") }, "pesos córtex → estriado, média das sementes");
  }
  if (experimento === "pong") {
    const segundos = resumos[0].segundos;
    console.log(`\n  sem cérebro, a mesma duração e as mesmas sementes:`);
    for (const politica of ["parada", "ao acaso", "seguidor"]) {
      const acertos = sementes.map((s) => pongSemCerebro(politica, s, segundos).acerto);
      linha(`    raquete ${politica}`, resumo(acertos));
    }
  } else console.log("\n  acaso: 25% (uma das 4 ações sorteada); a condição sem dopamina mostra o que a rede faz sem aprender");
}

function experimentoDeAprendizado(experimento) {
  if (!["escolha", "pong"].includes(experimento)) throw new Error(`experimento desconhecido: ${experimento}`);
  const sementes = lerArgumento("sementes", "1,2,3,4,5").split(",").map(Number);
  const segundos = Number(lerArgumento("segundos", experimento === "pong" ? 1800 : 2400));
  const perfil = lerArgumento("perfil", "roedor");
  const nivelCortex = lerArgumento("nivelCortex", "spikes");
  const condicoes = lerArgumento("condicoes", "com-dopamina,sem-dopamina").split(",").map((c) => c.replaceAll("-", " "));
  // --aproximar=<valor> (só no Pong) liga a recompensa por mover a raquete em direção à bola
  const aproximar = Number(lerArgumento("aproximar", 0));
  if (experimento === "pong") parametrosDoPong.recompensaPorAproximar = aproximar;
  // --sentidos=antigos|novos (só no Pong; ver sentidosDoPong)
  const sentidos = lerArgumento("sentidos", cerebroNoPong.sentidos);
  const sufixos = [
    nivelCortex === "spikes" ? "" : `-${nivelCortex}`,
    aproximar > 0 ? `-aproximar-${aproximar}` : "",
    experimento === "pong" && sentidos !== "novos" ? `-sentidos-${sentidos}` : "",
  ].join("");
  const pasta = lerArgumento("saida", join("resultados", "integrado", experimento + sufixos));
  if (!process.argv.includes("--analisar")) {
    const comSentidos = experimento === "pong" ? `, sentidos ${sentidos}` : "";
    console.log(`\nAprendizado (${experimento}): ${ligadasNoAprendizado.join(", ")}, acordado; córtex em ${nivelCortex}, perfil ${perfil}${comSentidos}, ${segundos} s, sementes ${sementes.join(", ")}; resumos em ${pasta}`);
    mkdirSync(pasta, { recursive: true });
    for (const condicao of condicoes) {
      for (const semente of sementes) {
        const r = rodarIntegrado(ligadasNoAprendizado, { segundos, semente, perfil, nivelCortex, tarefa: experimento, sentidos, ...condicoesDoAprendizado[condicao] });
        const resumo = { ...resumirAprendizado(experimento, condicao, semente, r), segundos };
        writeFileSync(join(pasta, `${nomeDaSemente(condicao, semente)}.json`), JSON.stringify(resumo));
        console.log(`  ${condicao}, semente ${semente}: ${resumo.segundosDeRelogio} s de relógio, acertos por quinto ${curvaDeAprendizado(resumo).map((x) => `${(100 * x).toFixed(0)}%`).join(" ")}`);
      }
    }
  }
  const resumos = readdirSync(pasta)
    .filter((nome) => nome.endsWith(".json"))
    .map((nome) => JSON.parse(readFileSync(join(pasta, nome), "utf8")))
    .filter((r) => sementes.includes(r.semente) && condicoes.includes(r.condicao));
  imprimirAprendizado(experimento, resumos, sementes);
}

// Rode com: node index.js --integrado [--perfil=roedor|humano] [--nivelCortex=spikes|populacao]
//           [--segundos=1440] [--semente=1] [--ate=vta] [--continuar] [--dias=5]
// Com --dias, roda esse número de dias seguidos com as regiões até --ate e mostra os pesos do
// córtex a cada adormecer e acordar; --noSono=escalonamento,stdp,istdp,recorrencia desliga essas
// peças do córtex enquanto o hipotálamo dorme (para achar a causa de uma mudança no sono).
// As regiões entram uma por vez, na ordem de ordemDasRegioes; cada uma só entra se o teste com e
// sem ela mostrar o córtex saudável e a assinatura da região (com --continuar, uma assinatura
// incompleta só avisa; o córtex doente sempre para). Um dia comprimido = 1440 s.
// Com --experimento=escolha|pong [--sementes=1,2,3,4,5] [--condicoes=com-dopamina,sem-dopamina]
// [--analisar], roda o experimento de aprendizado (ver experimentoDeAprendizado).
function demonstracaoIntegrado() {
  const experimento = lerArgumento("experimento", null);
  if (experimento) {
    experimentoDeAprendizado(experimento);
    return;
  }
  const perfil = lerArgumento("perfil", "roedor");
  const nivelCortex = lerArgumento("nivelCortex", "spikes");
  const segundos = Number(lerArgumento("segundos", 1440));
  const semente = Number(lerArgumento("semente", 1));
  const ate = lerArgumento("ate", ordemDasRegioes.at(-1));
  const continuar = process.argv.includes("--continuar");
  const dias = Number(lerArgumento("dias", 0));
  const noSono = lerArgumento("noSono", "").split(",").filter(Boolean);
  if (dias > 0) {
    const ligadas = ordemDasRegioes.slice(0, ordemDasRegioes.indexOf(ate) + 1);
    console.log(`\nModo integrado, ${dias} dias seguidos (${dias * 1440} s): ${ligadas.join(", ")}; perfil ${perfil}, córtex em ${nivelCortex}, semente ${semente}${noSono.length ? `; desligado no sono: ${noSono.join(", ")}` : ""}`);
    const nome = `${dias}-dias${noSono.length ? `-sem-${noSono.join("-")}-no-sono` : ""}`;
    const r = rodarIntegrado(ligadas, { segundos: dias * 1440, semente, perfil, nivelCortex, noSono, arquivoDeSondas: join("resultados", "integrado", `${nome}.sondas.csv`) });
    imprimirDias(r);
    return;
  }
  const pasta = join("resultados", "integrado");
  console.log(`\nModo integrado: perfil ${perfil}, córtex em ${nivelCortex}, ${segundos} s (1 min de hipotálamo por s), semente ${semente}`);
  console.log("  atrasos das vias (ms):");
  const sequencia = ordemDasRegioes.slice(0, ordemDasRegioes.indexOf(ate) + 1);
  const amostra = montarIntegrado(ordemDasRegioes, { semente, perfil, nivelCortex: "populacao" });
  for (const via of amostra.vias) {
    if (![via.origem, via.destino].every((nome) => nome === "ambiente" || sequencia.includes(nome))) continue;
    linha(`    ${via.origem}.${via.saida} → ${via.destino}.${via.entrada}`, via.atraso.toFixed(1));
  }
  let ligadas = [];
  let anterior = null;
  for (const nova of sequencia) {
    const com = rodarIntegrado([...ligadas, nova], { segundos, semente, perfil, nivelCortex, arquivoDeSondas: join(pasta, `${[...ligadas, nova].join("+")}.sondas.csv`) });
    if (anterior) imprimirComparacao(nova, anterior, com);
    else console.log(`\n${nova} sozinho (${com.segundosDeRelogio.toFixed(0)} s de relógio)`);
    if (nova === "nucleosDaBase") {
      // a mesma simulação com a recompensa de antes (independente da ação): as outras regiões não
      // podem mudar em nada, porque nenhuma via leva a escolha até elas
      const controle = rodarIntegrado([...ligadas, nova], { segundos, semente, perfil, nivelCortex, tarefa: "pistas" });
      com.controle = { semNucleos: anterior.impressao, comNucleos: controle.impressao };
      com.testeDaAlca = testarAlcaNoCortex({ nivel: nivelCortex, semente });
      imprimirPesosDaBase(com.pesosDaBase);
    }
    const problemas = saudeDoCortex(com);
    const assinatura = assinaturas[nova](com);
    for (const [descricao, ok] of assinatura) linha(`  ${ok ? "ok" : "FALHOU"}`, descricao);
    linha(`  ${problemas.length ? "FALHOU" : "ok"}`, problemas.length ? `córtex: ${problemas.join("; ")}` : "córtex saudável em todos os estados");
    if (problemas.length) {
      console.log(`\n${nova} não entra: o córtex não ficou saudável. As regiões seguintes ficam de fora.`);
      return;
    }
    if (assinatura.some(([, ok]) => !ok)) {
      if (!continuar) {
        console.log(`\n${nova} não entra: a assinatura falhou (use --continuar para seguir mesmo assim). As regiões seguintes ficam de fora.`);
        return;
      }
      console.log(`  ${nova} entra com a assinatura incompleta (--continuar); o córtex está saudável.`);
    }
    ligadas = [...ligadas, nova];
    anterior = com;
  }
  console.log(`\nRegiões ligadas: ${ligadas.join(", ")}. Sondas em ${pasta}.`);
}

// ============================================================================
// Visualização: serve visualizacao.html e transmite o cérebro por Server-Sent Events
//   GET  /          a página
//   GET  /estado    eventos "estrutura" (ao conectar e ao reiniciar), "quadro" (30/s) e "pesos" (4/s)
//   POST /controle  JSON com o que mudar: pausado, velocidade (ms simulados por segundo real),
//                   selecionado, estimular ("grupo" ou "selecionado"), recompensa, surpresa,
//                   reiniciar e as chaves de configuracaoCerebro que podem mudar com a rede rodando
// ============================================================================

function servirVisualizacao(cerebroInicial, porta = Number(process.env.PORT ?? 3000)) {
  let cerebro = cerebroInicial;
  const clientes = new Set();
  const execucao = { pausado: false, velocidade: 250 };
  const quadrosPorSegundo = 30;
  let msPendentes = 0;

  const enviar = (evento, dados, destinos = clientes) => {
    const mensagem = `event: ${evento}\ndata: ${JSON.stringify(dados)}\n\n`;
    for (const destino of destinos) destino.write(mensagem);
  };
  const pesos = () => cerebro.listaDeSinapses().map(({ w }) => Math.round(w * 1e5) / 1e5);

  setInterval(() => {
    if (!execucao.pausado) {
      msPendentes += execucao.velocidade / quadrosPorSegundo;
      const ms = Math.floor(msPendentes / cerebro.config.dt) * cerebro.config.dt;
      msPendentes -= ms;
      cerebro.simular(ms);
    }
    const { spikes, traco } = cerebro.esvaziarRegistro();
    if (clientes.size === 0) return;
    const { acetilcolina, noradrenalina, noradrenalinaFasica, dopaminaFasica } = cerebro.moduladores;
    const arredondar = (x) => Math.round(x * 1000) / 1000;
    enviar("quadro", {
      t: cerebro.t,
      v: cerebro.neuronios.map((n) => Math.round(n.v * 10) / 10),
      spikes,
      traco: traco.map((v) => Math.round(v * 10) / 10),
      selecionado: cerebro.selecionado,
      estado: cerebro.config.estado,
      moduladores: {
        acetilcolina: arredondar(acetilcolina),
        noradrenalina: arredondar(noradrenalina + noradrenalinaFasica),
        dopamina: arredondar(dopaminaFasica),
        plasticidade: arredondar(cerebro.efeitos.plasticidade),
      },
      ...execucao,
    });
  }, 1000 / quadrosPorSegundo);

  setInterval(() => {
    if (clientes.size > 0) enviar("pesos", pesos());
  }, 250);

  const controlar = (mudancas) => {
    if (typeof mudancas.pausado === "boolean") execucao.pausado = mudancas.pausado;
    if (Number.isFinite(mudancas.velocidade)) execucao.velocidade = Math.min(4000, Math.max(10, mudancas.velocidade));
    if (Number.isInteger(mudancas.selecionado) && mudancas.selecionado >= 0 && mudancas.selecionado < cerebro.n) {
      cerebro.selecionado = mudancas.selecionado;
    }
    if (mudancas.estimular === "grupo") cerebro.estimular(cerebro.grupo);
    if (mudancas.estimular === "selecionado") cerebro.estimular([cerebro.selecionado]);
    if (mudancas.recompensa === true) cerebro.recompensar();
    if (mudancas.surpresa === true) cerebro.surpreender();
    if (Object.hasOwn(estadosCerebrais, mudancas.estado)) cerebro.config.estado = mudancas.estado;
    for (const chave of ["entradaFundo", "razaoNMDA", "stp", "stdp", "escalonamento", "istdp"]) {
      if (typeof mudancas[chave] === typeof configuracaoCerebro[chave]) cerebro.config[chave] = mudancas[chave];
    }
    if (mudancas.reiniciar) {
      cerebro = new Cerebro(cerebro.config);
      enviar("estrutura", cerebro.estrutura());
      enviar("pesos", pesos());
    }
  };

  createServer(async (requisicao, resposta) => {
    try {
      if (requisicao.method === "GET" && requisicao.url === "/") {
        resposta.writeHead(200, { "Content-Type": "text/html; charset=utf-8" });
        resposta.end(await readFile(new URL("./visualizacao.html", import.meta.url)));
      } else if (requisicao.method === "GET" && requisicao.url === "/estado") {
        resposta.writeHead(200, { "Content-Type": "text/event-stream", "Cache-Control": "no-cache", Connection: "keep-alive" });
        enviar("estrutura", cerebro.estrutura(), [resposta]);
        enviar("pesos", pesos(), [resposta]);
        clientes.add(resposta);
        requisicao.on("close", () => clientes.delete(resposta));
      } else if (requisicao.method === "POST" && requisicao.url === "/controle") {
        let corpo = "";
        for await (const parte of requisicao) corpo += parte;
        controlar(JSON.parse(corpo));
        resposta.writeHead(204).end();
      } else {
        resposta.writeHead(404).end();
      }
    } catch (erro) {
      if (!resposta.headersSent) resposta.writeHead(erro instanceof SyntaxError ? 400 : 500);
      resposta.end();
    }
  }).listen(porta, () => console.log(`Cérebro ligado. Visualização em http://localhost:${porta}`));
}

// ============================================================================
// Visualização do Pong: o --integrado do experimento de aprendizado (córtex em spikes, prosencéfalo
// basal, locus coeruleus, VTA e núcleos da base, acordado) joga contra um algoritmo (ver criarPong).
// O cérebro continua aprendendo enquanto joga, só com a recompensa das próprias rebatidas.
//   GET  /          pong.html
//   GET  /estado    eventos "estrutura" (ao conectar e ao reiniciar) e "quadro" (30/s)
//   POST /controle  JSON com o que mudar: pausado, velocidade (ms simulados por segundo real; 0 é o
//                   máximo que der), adversario ({ tipo, velocidade, reacao, erro }), zerarPlacar (o cérebro
//                   continua o mesmo) e reiniciar ({ semente, comDopamina })
// Rode com: node index.js --pong [--treino=1800] [--carregar[=<arquivo>]] [--soTreinar] [--semente=1]
//           [--semDopamina] [--aproximar=0.1] [--sentidos=novos|antigos] [--fisica=nossa|manus]
// Com --treino, o cérebro joga esse tempo (s simulados) antes de a página abrir (na nossa física
// contra o seguidor, na do Manus contra o v1), e o que ele aprendeu é salvo em
// resultados/integrado/cerebros/ (ver salvarCerebro). --carregar começa de um cérebro salvo (o da
// semente, dos sentidos e da física, ou o arquivo dado), e os dois juntos continuam o treino de um
// salvo. --soTreinar treina, salva e sai, sem abrir a página. --aproximar liga a recompensa por mover
// a raquete em direção à bola (ver parametrosDoPong). O botão "Salvar cérebro" salva o de agora.
// ============================================================================

// O arquivo padrão do cérebro salvo de cada semente, sentidos e física
const arquivoDoCerebro = (semente, comDopamina = true, sentidos = cerebroNoPong.sentidos, fisica = "nossa") =>
  join(
    "resultados",
    "integrado",
    "cerebros",
    `pong-semente-${semente}${comDopamina ? "" : "-sem-dopamina"}${sentidos === "novos" ? "" : `-sentidos-${sentidos}`}${fisica === "nossa" ? "" : `-fisica-${fisica}`}.json.gz`,
  );

// Os nomes dos canais do córtex em cada sentido do Pong, para a página
const nomesDosCanaisDoPong = {
  antigos: ["bola acima", "bola abaixo", "subir", "descer"],
  novos: ["bola acima", "bola abaixo", "bola subindo", "bola descendo", "subir", "descer"],
};

function servirPong({
  semente = 1,
  comDopamina = true,
  treino = 0,
  carregar = null,
  soTreinar = false,
  sentidos = cerebroNoPong.sentidos,
  fisica = "nossa",
  porta = Number(process.env.PORT ?? 3000),
} = {}) {
  const quadrosPorSegundo = 30;
  // A mesma referência fica no ambiente, então muda ao vivo. O padrão é o excelente com a velocidade
  // de raquete do cérebro e erro 0,4. Contra o cérebro da semente 1 treinado 30 min, em ~14 min de
  // jogo, o placar foi 0 × 146 com erro 0,2, 2 × 142 com 0,3 e 6 × 98 com 0,4 (um jogador reativo
  // roteirizado, mais preciso que o cérebro, faz ~10% dos pontos com 0,2). O pré-treino é contra o
  // seguidor: contra o excelente o cérebro quase não acerta e aprende mal.
  const adversario = { tipo: "excelente", velocidade: parametrosDoPong.velocidadeDaRaquete, reacao: 50, erro: 0.4 };
  const adversarioDoTreino = { tipo: "seguidor", velocidade: 0.4, reacao: 300, erro: 0 };
  const execucao = { pausado: false, velocidade: 1000 };
  const clientes = new Set();
  let jogo = null;
  let pendentes = 0;

  const montar = () => {
    const integrado = montarIntegrado(ligadasNoAprendizado, { semente, comDopamina, tarefa: "pong", nivelCortex: "spikes", adversario, sentidos, fisica });
    const { ambiente, cortex, nucleosDaBase, vta } = integrado.regioes;
    // resultados: 1 rebatida, 0 erro; curva: a fração de rebatidas a cada bloco de 20 jogadas;
    // experienciaAnterior: os s simulados que um cérebro carregado já tinha jogado
    jogo = { integrado, ambiente, cortex, nucleosDaBase, vta, lidos: 0, resultados: [], curva: [], amostras: [], eventos: [], experienciaAnterior: 0, arquivo: null };
  };
  const experiencia = () => Math.round(jogo.experienciaAnterior + jogo.integrado.t / 1000);

  // O que o cérebro aprendeu (córtex, núcleos da base e VTA) e o histórico de rebatidas, num .json.gz.
  // Os estados rápidos (voltagens, condutâncias, traços) não vão: em poucos ms eles se refazem.
  const salvarCerebro = (arquivo = arquivoDoCerebro(semente, comDopamina, sentidos, fisica)) => {
    mkdirSync(dirname(arquivo), { recursive: true });
    const { cortex, nucleosDaBase, vta } = jogo;
    const salvo = {
      versao: 2,
      semente,
      comDopamina,
      sentidos,
      fisica,
      experiencia: experiencia(),
      cortex: cortex.aprendido(),
      nucleosDaBase: nucleosDaBase.aprendido(),
      vta: vta.aprendido(),
      resultados: jogo.resultados,
      curva: jogo.curva,
    };
    writeFileSync(arquivo, gzipSync(JSON.stringify(salvo)));
    jogo.arquivo = arquivo;
    return arquivo;
  };
  // Monta um cérebro novo com a semente do arquivo (a mesma fiação) e põe nele o que foi aprendido
  const carregarCerebro = (arquivo) => {
    const salvo = JSON.parse(gunzipSync(readFileSync(arquivo)).toString("utf8"));
    semente = salvo.semente;
    comDopamina = salvo.comDopamina;
    sentidos = salvo.sentidos ?? "antigos"; // a versão 1 só tinha os sentidos antigos
    fisica = salvo.fisica ?? "nossa";
    montar();
    jogo.cortex.carregar(salvo.cortex);
    jogo.nucleosDaBase.carregar(salvo.nucleosDaBase);
    jogo.vta.carregar(salvo.vta);
    Object.assign(jogo, { resultados: salvo.resultados, curva: salvo.curva, experienciaAnterior: salvo.experiencia, arquivo });
  };

  // Anda até `ms` milissegundos simulados ou até `limite` ms de relógio. Guarda a cada 10 ms uma
  // amostra [t, dopamina com pausas, a alça de cada canal, a taxa de cada canal] e lê o diário do
  // ambiente.
  const andar = (ms, limite = Infinity, guardar = true) => {
    const inicio = performance.now();
    const { integrado, ambiente, cortex, nucleosDaBase, vta } = jogo;
    const canais = sentidosDoPong[sentidos].canais;
    let feitos = 0;
    while (feitos < ms && performance.now() - inicio < limite) {
      integrado.passo(1);
      feitos++;
      if (guardar && Math.round(integrado.t) % 10 === 0) {
        const arredondar = (x) => Math.round(x * 1000) / 1000;
        jogo.amostras.push(
          integrado.t,
          arredondar(vta.saidas.dopaminaComPausas),
          ...canais.map((_, k) => arredondar(nucleosDaBase.saidas[`alca${k}`])),
          ...canais.map((_, k) => arredondar(cortex.saidas[`canal${k}`])),
        );
      }
    }
    for (; jogo.lidos < ambiente.diario.length; jogo.lidos++) {
      const { t, tipo } = ambiente.diario[jogo.lidos];
      if (guardar) jogo.eventos.push({ t, tipo });
      if (tipo !== "rebatida" && tipo !== "erro") continue;
      jogo.resultados.push(tipo === "rebatida" ? 1 : 0);
      if (jogo.resultados.length % 20 === 0) jogo.curva.push(media(jogo.resultados.slice(-20)));
    }
    return feitos;
  };

  const estrutura = () => ({
    nExc: jogo.cortex.cerebro.config.nExc,
    nInib: jogo.cortex.cerebro.config.nInib,
    canais: sentidosDoPong[sentidos].canais.map((canal) => [canal[0], canal.at(-1)]),
    nomesDosCanais: nomesDosCanaisDoPong[sentidos],
    acoes: sentidosDoPong[sentidos].acoes,
    entradas: sentidosDoPong[sentidos].entradas,
    sentidos,
    fisica,
    semente,
    comDopamina,
    acaso: 0.22, // a raquete com ações ao acaso (pongSemCerebro), nas sementes 1 a 5
    experienciaAnterior: jogo.experienciaAnterior,
    arquivo: jogo.arquivo,
  });

  if (carregar) {
    if (!existsSync(carregar)) {
      console.error(`Não achei ${carregar}. Treine e salve antes com: node index.js --pong --treino=1800 --soTreinar --semente=${semente}`);
      process.exit(1);
    }
    carregarCerebro(carregar);
    console.log(`Cérebro carregado de ${carregar}: semente ${semente}, ${Math.round(jogo.experienciaAnterior / 60)} min de jogo, ${jogo.resultados.length} jogadas.`);
  } else montar();
  if (treino > 0) {
    const daPartida = { ...adversario };
    Object.assign(adversario, adversarioDoTreino);
    const contra = fisica === "manus" ? "v1 do Manus" : adversario.tipo;
    console.log(`Treinando ${treino} s simulados contra o ${contra} (sentidos ${sentidos}, física ${fisica}) antes de abrir a página (o cérebro em spikes anda ~4× mais rápido que o tempo real)…`);
    for (let feito = 0; feito < treino; feito += 60) {
      andar(Math.min(60, treino - feito) * 1000, Infinity, false);
      const ultimas = jogo.resultados.slice(-50);
      console.log(`  ${Math.min(treino, feito + 60)} s: ${jogo.resultados.length} jogadas, rebatidas nas últimas 50 ${(100 * media(ultimas)).toFixed(0)}% · placar ${jogo.ambiente.placar.cerebro} × ${jogo.ambiente.placar.algoritmo}`);
    }
    Object.assign(adversario, daPartida);
    Object.assign(jogo.ambiente.placar, { cerebro: 0, algoritmo: 0 });
    console.log(`Treino feito; cérebro salvo em ${salvarCerebro()}.`);
    if (soTreinar) return;
    console.log(`A partida começa contra o ${fisica === "manus" ? "v1 do Manus" : adversario.tipo}, com o placar zerado.`);
  }
  jogo.cortex.spikesRecentes = [];

  const enviar = (evento, dados, destinos = clientes) => {
    const mensagem = `event: ${evento}\ndata: ${JSON.stringify(dados)}\n\n`;
    for (const destino of destinos) destino.write(mensagem);
  };

  setInterval(() => {
    if (!execucao.pausado) {
      if (execucao.velocidade > 0) {
        pendentes += execucao.velocidade / quadrosPorSegundo;
        const feitos = andar(Math.floor(pendentes), 25);
        // se o computador não acompanha, a simulação fica mais lenta em vez de acumular atraso
        pendentes = Math.min(pendentes - feitos, execucao.velocidade / quadrosPorSegundo);
      } else andar(Infinity, 25);
    }
    const { integrado, ambiente, cortex, nucleosDaBase } = jogo;
    const spikes = cortex.spikesRecentes;
    const amostras = jogo.amostras;
    const eventos = jogo.eventos;
    cortex.spikesRecentes = [];
    jogo.amostras = [];
    jogo.eventos = [];
    if (clientes.size === 0) return;
    const resultados = jogo.resultados;
    enviar("quadro", {
      t: integrado.t,
      posicoes: ambiente.posicoes(),
      placar: ambiente.placar,
      fisica,
      jogadas: resultados.length,
      rebatidas: somar(resultados),
      ultimas: resultados.slice(-50).join(""),
      curva: jogo.curva,
      amostras,
      spikes,
      eventos,
      pesos: nucleosDaBase.W.map((linhaW) => Array.from(linhaW, (w) => Math.round(w * 1000) / 1000)),
      adversario,
      ...execucao,
    });
  }, 1000 / quadrosPorSegundo);

  const controlar = (mudancas) => {
    if (typeof mudancas.pausado === "boolean") execucao.pausado = mudancas.pausado;
    if (Number.isFinite(mudancas.velocidade)) execucao.velocidade = mudancas.velocidade <= 0 ? 0 : Math.min(8000, Math.max(50, mudancas.velocidade));
    if (mudancas.zerarPlacar === true) Object.assign(jogo.ambiente.placar, { cerebro: 0, algoritmo: 0 });
    if (mudancas.salvar === true) {
      const arquivo = salvarCerebro();
      console.log(`Cérebro salvo em ${arquivo} (${Math.round(experiencia() / 60)} min de jogo).`);
      enviar("estrutura", estrutura());
    }
    if (mudancas.adversario) {
      const { tipo, velocidade, reacao, erro } = mudancas.adversario;
      if (tiposDeAdversario.includes(tipo)) adversario.tipo = tipo;
      if (Number.isFinite(erro)) adversario.erro = Math.min(1, Math.max(0, erro));
      if (Number.isFinite(velocidade)) adversario.velocidade = Math.min(2, Math.max(0, velocidade));
      if (Number.isFinite(reacao)) adversario.reacao = Math.min(900, Math.max(0, reacao));
    }
    if (mudancas.reiniciar) {
      if (Number.isInteger(mudancas.reiniciar.semente) && mudancas.reiniciar.semente > 0) semente = mudancas.reiniciar.semente;
      if (typeof mudancas.reiniciar.comDopamina === "boolean") comDopamina = mudancas.reiniciar.comDopamina;
      montar();
      jogo.cortex.spikesRecentes = [];
      pendentes = 0;
      enviar("estrutura", estrutura());
    }
  };

  createServer(async (requisicao, resposta) => {
    try {
      if (requisicao.method === "GET" && requisicao.url === "/") {
        resposta.writeHead(200, { "Content-Type": "text/html; charset=utf-8" });
        resposta.end(await readFile(new URL("./pong.html", import.meta.url)));
      } else if (requisicao.method === "GET" && requisicao.url === "/estado") {
        resposta.writeHead(200, { "Content-Type": "text/event-stream", "Cache-Control": "no-cache", Connection: "keep-alive" });
        enviar("estrutura", estrutura(), [resposta]);
        clientes.add(resposta);
        requisicao.on("close", () => clientes.delete(resposta));
      } else if (requisicao.method === "POST" && requisicao.url === "/controle") {
        let corpo = "";
        for await (const parte of requisicao) corpo += parte;
        controlar(JSON.parse(corpo));
        resposta.writeHead(204).end();
      } else {
        resposta.writeHead(404).end();
      }
    } catch (erro) {
      if (!resposta.headersSent) resposta.writeHead(erro instanceof SyntaxError ? 400 : 500);
      resposta.end();
    }
  }).listen(porta, () =>
    console.log(`Pong ligado: cérebro (semente ${semente}, sentidos ${sentidos}${comDopamina ? "" : ", sem dopamina"}) × algoritmo, física ${fisica}. Visualização em http://localhost:${porta}`),
  );
}

function demonstracaoPong() {
  parametrosDoPong.recompensaPorAproximar = Number(lerArgumento("aproximar", 0));
  const semente = Number(lerArgumento("semente", 1));
  const comDopamina = !process.argv.includes("--semDopamina");
  const sentidos = lerArgumento("sentidos", cerebroNoPong.sentidos);
  const fisica = lerArgumento("fisica", "nossa");
  if (!(sentidos in sentidosDoPong) || !["nossa", "manus"].includes(fisica)) throw new Error("use --sentidos=novos|antigos e --fisica=nossa|manus");
  const carregar = lerArgumento("carregar", process.argv.includes("--carregar") ? arquivoDoCerebro(semente, comDopamina, sentidos, fisica) : null);
  servirPong({ semente, comDopamina, carregar, sentidos, fisica, treino: Number(lerArgumento("treino", 0)), soTreinar: process.argv.includes("--soTreinar") });
}

// ============================================================================
// Escolhe o que rodar: node index.js --01 (ou --02, --03, --04, --05, --cerebro, --conectoma,
// --integrado) roda uma demonstração e sai; --pong liga a visualização do cérebro jogando Pong contra
// um algoritmo; --fila=<arquivo> roda uma fila de tarefas do --conectoma; sem argumento, liga o
// cérebro com a visualização.
// ============================================================================

const demonstracoes = {
  "--01": demonstracao01,
  "--02": demonstracao02,
  "--03": demonstracao03,
  "--04": demonstracao04,
  "--05": demonstracao05,
  "--cerebro": demonstracaoCerebro,
  "--conectoma": demonstracaoConectoma,
  "--integrado": demonstracaoIntegrado,
  "--pong": demonstracaoPong,
};
const argumentoSemente = process.argv.find((argumento) => argumento.startsWith("--semente="));
if (argumentoSemente) semear(Number(argumentoSemente.split("=")[1]));
const demonstracao = process.argv.find((argumento) => argumento in demonstracoes);
// --fila=<arquivo> roda tarefas do --conectoma em processos paralelos (ver rodarFila)
if (process.argv.some((argumento) => argumento.startsWith("--fila="))) rodarFila();
else if (demonstracao) demonstracoes[demonstracao]();
else brain();