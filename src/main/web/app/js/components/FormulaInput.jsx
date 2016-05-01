import React from 'react'

let FormulaInput = ({ onEnterPress }) => {

  let input

  return (
    <div>
      <input 
        ref={node => {
          input = node
        }}
        onKeyPress={e => {
          if (e.key == 'Enter') {
            onEnterPress(input.value)
            input.value=''
          }
        }}/>
    </div>
  )
}

export default FormulaInput

