import type {Metadata} from 'next';
import './globals.css';
export const metadata:Metadata={title:'Dresden Codex Observatory',description:'Explore the Dresden Codex through exact calendar arithmetic, published eclipse stations, Venus tables and a complete lunar interval census.',icons:{icon:'/favicon.svg',shortcut:'/favicon.svg'}};
export default function RootLayout({children}:{children:React.ReactNode}){return <html lang="en"><body>{children}</body></html>;}
