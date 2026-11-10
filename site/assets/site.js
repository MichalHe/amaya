// Behaviour shared by the pages of the website: the theme toggle, copy buttons, tabs, and the automaton of the
// landing page.
import { mountHero } from './hero.js';

const root = document.documentElement;

function effectiveTheme() {
  if (root.dataset.theme) return root.dataset.theme;
  return window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
}

for (const button of document.querySelectorAll('.theme-toggle')) {
  const label = () => button.setAttribute('aria-label', `Switch to the ${effectiveTheme() === 'dark' ? 'light' : 'dark'} theme`);
  label();
  button.addEventListener('click', () => {
    const theme = effectiveTheme() === 'dark' ? 'light' : 'dark';
    root.dataset.theme = theme;
    try { localStorage.setItem('amaya-theme', theme); } catch (e) { /* not saved */ }
    label();
    document.dispatchEvent(new CustomEvent('amaya-theme-change'));
  });
}

// A copy button for every code block.
for (const block of document.querySelectorAll('.code')) {
  const button = document.createElement('button');
  button.type = 'button';
  button.className = 'copy';
  button.textContent = 'Copy';
  button.addEventListener('click', async () => {
    try {
      await navigator.clipboard.writeText(block.querySelector('pre').innerText.trimEnd() + '\n');
      button.textContent = 'Copied';
    } catch (e) {
      button.textContent = 'Press Ctrl+C';
    }
    setTimeout(() => { button.textContent = 'Copy'; }, 1500);
  });
  block.append(button);
}

// Tabs: <div class="tabs" role="tablist"> with buttons aria-controls'ing the panels.
for (const list of document.querySelectorAll('.tabs')) {
  const tabs = [...list.querySelectorAll('[role="tab"]')];
  const select = (tab) => {
    for (const other of tabs) {
      const selected = other === tab;
      other.setAttribute('aria-selected', String(selected));
      other.tabIndex = selected ? 0 : -1;
      document.getElementById(other.getAttribute('aria-controls')).hidden = !selected;
    }
  };
  tabs.forEach((tab, i) => {
    tab.addEventListener('click', () => select(tab));
    tab.addEventListener('keydown', (event) => {
      const step = { ArrowRight: 1, ArrowLeft: -1 }[event.key];
      if (!step) return;
      const next = tabs[(i + step + tabs.length) % tabs.length];
      select(next);
      next.focus();
    });
  });
}

const hero = document.getElementById('hero-automaton');
if (hero) mountHero(hero);
