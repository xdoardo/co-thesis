const { Marp } = require('@marp-team/marp-core');
const Prism = require('prismjs');
//const hljsDefineIECST = require('highlightjs-structured-text')
//
//hljsDefineIECST(hljs);

const loadLanguages = require('prismjs/components/');
loadLanguages(['agda', 'coq', 'hs']);

module.exports = (opts) => {
  const marp = new Marp(opts);

  marp.highlighter = (code, lang) => {
    if (lang == 'agda') {
      return Prism.highlight(code, Prism.languages.agda, 'agda');
    } else if (lang == 'coq') {
      return Prism.highlight(code, Prism.languages.coq, 'coq');
    } else if (lang == 'hs') {
      return Prism.highlight(code, Prism.languages.hs, 'hs');
    } else {
      return '';
    }
  };

  return marp;
};
