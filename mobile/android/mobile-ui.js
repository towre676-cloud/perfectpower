const mobileMenu=document.getElementById('mobile-menu');
mobileMenu.addEventListener('click',()=>{
 const dialog=document.getElementById('mobile-navigation'),holder=dialog.querySelector('.mobile-links');
 holder.replaceChildren();
 for(const item of document.querySelectorAll('#nav button')){const clone=item.cloneNode(true);clone.addEventListener('click',()=>{location.hash=item.dataset.route;dialog.close();});holder.append(clone);}
 const settings=document.createElement('button');settings.textContent='Appearance & coverage';settings.addEventListener('click',()=>{location.hash='settings';dialog.close();});holder.append(settings);dialog.showModal();
});
document.getElementById('close-mobile-menu').addEventListener('click',()=>document.getElementById('mobile-navigation').close());
window.addEventListener('hashchange',()=>{setTimeout(()=>document.querySelector('#nav button.active')?.scrollIntoView({block:'nearest',inline:'nearest'}),40);});
