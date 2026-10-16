import { DurableObject } from "cloudflare:workers";
export class LeanDbHost extends DurableObject {
  async ready() {
    const c=this.ctx.container!;
    if(!c.running) c.start({enableInternet:true});
    await c.setInactivityTimeout(1800000);
    for(let i=0;i<45;i++) {
      try { const r=await c.getTcpPort(8080).fetch("http://container/health"); if(r.ok) return; } catch {}
      await new Promise(r=>setTimeout(r,1000));
    }
    throw new Error("container not ready");
  }
  async fetch(req:Request) {
    const url=new URL(req.url), action=url.pathname.split("/").pop();
    if(action==="destroy") {await this.ctx.container!.destroy();return Response.json({ok:true});}
    await this.ready();
    let target=action==="workspace"?"/workspace?dir=/work/repo":action==="exec"?"/env/exec":action==="call"?"/env/call":"/health";
    return this.ctx.container!.getTcpPort(8080).fetch(new Request("http://container"+target,req));
  }
}
export default {
 async fetch(req:Request,env:any) {
   if(req.headers.get("Authorization")!=="Bearer "+env.ADMIN_TOKEN) return Response.json({ok:false},{status:401});
   return env.HOSTS.get(env.HOSTS.idFromName("cf-v1:durable")).fetch(req);
 }
};
