import assert from 'node:assert/strict';
import path from 'node:path';
import React from 'react';
import {renderToStaticMarkup} from 'react-dom/server';
import {createServer} from 'vite';
const server=await createServer({configFile:path.resolve('vite.standalone.config.ts'),server:{middlewareMode:true},appType:'custom'});
try{
 const {default:Observatory}=await server.ssrLoadModule('/@fs/'+path.resolve('app/page.tsx'));
 for(const [view,expected]of [['calendar','Ask the calendars'],['eclipse','From raw numeral'],['venus','A trillion rounds'],['lunar','Restrict the corpus'],['restarts','Select a prediction'],['sources','Follow a claim']]){
  const html=renderToStaticMarkup(React.createElement(Observatory,{initialView:view}));
  assert.ok(html.includes(expected),view);assert.ok(html.includes('Export experiment'),view);assert.ok(html.includes('Lean source'),view);if(view==='calendar')assert.ok(html.includes('Restrict the calendar population'),view);assert.ok(!html.includes('NaN'),view);
  console.log(`PASS ${view}: primary view and deep research panel render (${html.length} HTML bytes).`);
 }
}finally{await server.close();}
