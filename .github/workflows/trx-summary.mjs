// Сводка .trx (dotnet test --logger trx) в Markdown для GITHUB_STEP_SUMMARY: число тестов по сборкам и все падения.
// --annotations: вместо Markdown — строки ::error на каждое падение; их видно через API check-runs
// (логи и артефакты лежат в blob-хранилище, которое из внутренней сети недоступно).
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const dir = process.argv[2] ?? 'TestResults';
const annotate = process.argv.includes('--annotations');
let files = [];
try { files = readdirSync(dir).filter(f => f.endsWith('.trx')); } catch { }
const attr = (s, name) => (s.match(new RegExp(`${name}="([^"]*)"`)) ?? [])[1];
const unxml = s => s.replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"').replace(/&apos;/g, "'").replace(/&amp;/g, '&');
const escData = s => s.replace(/%/g, '%25').replace(/\r/g, '').replace(/\n/g, '%0A');
const escProp = s => escData(s).replace(/:/g, '%3A').replace(/,/g, '%2C');
const rows = [], fails = [];
for (const f of files) {
  const x = readFileSync(join(dir, f), 'utf8');
  const c = x.match(/<Counters [^>]*>/)?.[0] ?? '';
  const storage = attr(x, 'storage') ?? f;
  const asm = storage.split(/[\\/]/).pop();
  rows.push(`| ${asm} | ${attr(c, 'total')} | ${attr(c, 'passed')} | ${attr(c, 'failed')} |`);
  for (const m of x.matchAll(/<UnitTestResult [^>]*outcome="Failed"[^>]*>([\s\S]*?)<\/UnitTestResult>/g)) {
    const name = unxml(attr(m[0], 'testName') ?? '?');
    const msg = unxml((m[1].match(/<Message>([\s\S]*?)<\/Message>/) ?? [])[1] ?? '').slice(0, 1500);
    fails.push({ asm, name, msg });
  }
}
if (annotate) {
  for (const f of fails.slice(0, 50)) console.log(`::error title=${escProp(`${f.asm}: ${f.name}`.slice(0, 200))}::${escData(f.msg)}`);
  process.exit(0);
}
console.log('| сборка | всего | прошло | упало |\n|---|---|---|---|');
console.log(rows.join('\n') || '| (нет .trx) | | | |');
console.log(fails.length
  ? `\n## Падения (${fails.length})\n\n` + fails.map(f => `### ${f.asm}: ${f.name}\n\n\`\`\`\n${f.msg}\n\`\`\``).join('\n\n')
  : '\nПадений нет.');
