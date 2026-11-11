// Applies the saved colour theme before the page is painted, so that it does not flash.
(function () {
  try {
    var theme = localStorage.getItem('amaya-theme');
    if (theme === 'light' || theme === 'dark') document.documentElement.dataset.theme = theme;
  } catch (e) {
    // Storage is unavailable; the theme follows the system preference.
  }
})();
