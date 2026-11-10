// Checks the automaton of the landing page (site/assets/hero.js): it must accept exactly the integers congruent
// to 1 modulo 3, under the encoding the widget uses (two's complement, least significant bit first, the last bit
// being the sign), also when the encoding is padded by repeating the sign bit.
//
//   node site/test/hero.mjs
import { parseAutomaton, encode, run } from '../assets/hero.js';

const automaton = parseAutomaton();
let failures = 0;
for (let n = -2000; n <= 2000; n += 1) {
  const bits = encode(n);
  const value = bits.slice(0, -1).reduce((sum, bit, i) => sum + bit * 2 ** i, 0) - bits.at(-1) * 2 ** (bits.length - 1);
  if (value !== n) { failures += 1; console.log(`FAIL encode(${n}) = ${bits} means ${value}`); continue; }
  const expected = ((n % 3) + 3) % 3 === 1;
  for (const padding of [0, 1, 4]) {
    const padded = [...bits, ...Array(padding).fill(bits.at(-1))];
    if (run(automaton, padded).accepted !== expected) {
      failures += 1;
      if (failures < 10) console.log(`FAIL ${n} with ${padding} padding bits: accepted=${!expected}`);
    }
  }
}
console.log(failures ? `${failures} failure(s)` : 'ok   hero automaton accepts exactly x mod 3 = 1 on -2000..2000');
process.exit(failures ? 1 : 0);
