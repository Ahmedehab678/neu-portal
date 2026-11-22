FROM node:22-slim
WORKDIR /app
COPY package.json server.js index.html ./
ENV DATA_DIR=/data PORT=3000
EXPOSE 3000
CMD ["npm","start"]
