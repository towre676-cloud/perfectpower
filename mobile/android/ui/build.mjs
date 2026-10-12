import {build} from 'esbuild';
import {mkdirSync,copyFileSync} from 'node:fs';
mkdirSync('dist',{recursive:true});
await build({entryPoints:['app.js'],bundle:true,minify:true,format:'esm',outfile:'dist/app.js',legalComments:'linked'});
for(const name of ['index.html','style.css','brand.svg','portfolio_geometry.css'])copyFileSync(name,'dist/'+name);
